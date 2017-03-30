/*
 * Copyright (C) 2013 Bastian Bloessl <bloessl@ccs-labs.org>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
#include <ieee802_15_4/mac.h>
#include <gnuradio/io_signature.h>
#include <gnuradio/block_detail.h>
#include <sstream>
//#include <list>
#include <cstdlib>

#include <iostream>
#include <iomanip>
#include <boost/thread.hpp>
#include <boost/date_time.hpp>
#include <stdio.h>
#include <stddef.h>
#include <sys/time.h>
#include <string>

#include "SendPackage.h"

using namespace gr::ieee802_15_4;

class mac_impl : public mac {
    float lastAvPower = -1000.0;
    float referenceValueChannelBusy = -80; // number of chanel power
    std::list<SendPackage*> sendList;
    long int slotSize = 2; //milisecounds
    long int cw_backoff_min = 4; //number of slots
    long int cw_backoff_max = 64; //number of slots
    long int cw_current_backoff = 4;//number of slots
    long int real_backoff = 4;//number of slots
    long int difs = 5;//milisecounds
    long int sifs = 2;//milisecounds
    long int resend_waiting = 80;//milisecounds

    short max_retr = 5;
    bool conection_state = false;
    bool rts_send = false;

    /*comand filter     */
    char cmd_rts = 0x01;                //association request TX
    char cmd_cts = 0x02;                //association response RX
    char cmd_end_communication = 0x03;   //disassociation notification TX/RX
    char cmd_data_request = 0x04;       //data request TX
    char cmd_realignment = 0x08;        //Coordinator realignment

    //Endereço MAC local. Os endereços possuem 2 bytes, assim, essas duas
    //variáveis representam apenas um endereço. Para testes, esse endereço deve
    //ser mudado para cada máquina. Deve-se lembrar de manter a coerência com
    //os endereços de outras máquinas atribuidos na função start() e com a
    //chamada da função generate_mac() feita na função app_in().
    char mac_addr_1 = 0x41;
    char mac_addr_2 = 0xe8;

    //Endereço de broadcast
    char addr_bc_1 = 0xff;
    char addr_bc_2 = 0xff;

    //Endereços de outras máquinas para simulações
    char addr0[2];
    char addr1[2]; //sem uso
    char addr2[2]; //sem uso

    //array que vai conter os endereços das outras máquinas
    char* addrs[3];

    boost::shared_ptr<gr::thread::thread> exec;
    boost::shared_ptr<gr::thread::thread> waitSending;
    boost::condition_variable cond;
    boost::condition_variable cond2;
    boost::mutex mut;
    boost::mutex mut2;
    bool data_ready = false;
    bool lastPackAckedOrTimeToResendFinished = false;

public:

#define dout d_debug && std::cout

    mac_impl(bool debug) :
    block("mac",
    gr::io_signature::make(0, 0, 0),
    gr::io_signature::make(0, 0, 0)),
    d_msg_offset(0),
    d_seq_nr(0),
    d_debug(debug),
    d_num_packet_errors(0),
    d_num_packets_received(0) {

        message_port_register_in(pmt::mp("cs in"));
        set_msg_handler(pmt::mp("cs in"), boost::bind(&mac_impl::cs_in, this, _1));
        message_port_register_in(pmt::mp("app in"));
        set_msg_handler(pmt::mp("app in"), boost::bind(&mac_impl::app_in, this, _1));
        message_port_register_in(pmt::mp("pdu in"));
        set_msg_handler(pmt::mp("pdu in"), boost::bind(&mac_impl::mac_in, this, _1));

        message_port_register_out(pmt::mp("app out"));
        message_port_register_out(pmt::mp("pdu out"));
    }

    ~mac_impl(void) {
    }

    /**Função que trata as entradas da conexão "pdu in".
     * Recebe mensagens que contêm pacotes MAC
     * @param msg Mensagem com pacotes MAC (Dados ou acks)     */
    void mac_in(pmt::pmt_t msg) {
        pmt::pmt_t blob;
        char* request = (char*)malloc(sizeof(char)*1);
        char packRequest[256];
        if (pmt::is_pair(msg)) {
            blob = pmt::cdr(msg);
            dout << "Message received" << std::endl;
        }
        else {// erro de formato
            assert(false);
        }

        size_t data_len = pmt::blob_length(blob);
        //LOG printf("Tamanho do pacote recebido: %d\n", data_len);

        if (data_len < 11 && data_len != 5) {  // Interferência
            dout << "MAC: frame too short. Dropping!" << std::endl;
            dout<<"Ruido\n"<< std::endl;
            return;
        }

        char* recPackage = (char*) pmt::blob_data(blob);
        uint16_t crc = crc16(recPackage, data_len);

        //LOG std::cout << "Número de pacotes recebidos: " << d_num_packets_received << std::endl;

        if (crc) {
            d_num_packet_errors++;
            dout << "MAC: wrong crc. Dropping packet!" << std::endl;
            return;
        }
        else {
            if (isAckPack(recPackage)) {
                //LOG printf("Package %u acked.\n\n", (unsigned char)recPackage[2]);
                removePackAcked(recPackage);
            }
            // RTS Received
            else if((mac_addr_1 != recPackage[7] || mac_addr_2 != recPackage[8]) &&
                    (mac_addr_1 == recPackage[5] && mac_addr_2 == recPackage[6]) &&
                    (recPackage[9] == cmd_rts)){
                char end [2];
                addrs[0][0]=recPackage[7];                                              //atualiza lista de endereço
                addrs[0][1]=recPackage[8];

                dout<<"RTS received\n"<< std::endl;
                conection_state = true;
                end[0]=recPackage[7];
                end[1] = recPackage[8];
                // send CTS
                generate_and_send_cmd(request, 0, packRequest , addr0, cmd_cts);
                dout<<"Sending CTS\n"<< std::endl;
                sendAck(recPackage);
            }

            else if((mac_addr_1 != recPackage[7] || mac_addr_2 != recPackage[8]) &&
                    (mac_addr_1 == recPackage[5] && mac_addr_2 == recPackage[6]) &&
                    (recPackage[9] == cmd_cts)) {
                dout << "CTS received\n" << std::endl;
                d_num_packets_received++;

                conection_state = true;
                // addrs[0][0]=recPackage[7]; //atualiza lista de endereço
                // addrs[0][1]=recPackage[8];
                sendAck(recPackage);
            }

            else if((mac_addr_1 != recPackage[7] || mac_addr_2 != recPackage[8]) &&
                    (mac_addr_1 == recPackage[5] && mac_addr_2 == recPackage[6]) &&
                    (recPackage[9] == cmd_end_communication)) {
                dout<<"Received end of communication\n"<< std::endl;
                dout << "MAC: exiting" << std::endl;
                //detail().get()->set_done(true);
                sendAck(recPackage);
            }
                //Pacote Dados
            else if((mac_addr_1 != recPackage[7] || mac_addr_2 != recPackage[8]) &&
                    (mac_addr_1 == recPackage[5] && mac_addr_2 == recPackage[6]) &&
                    (addrs[0][0] == recPackage[7] &&  addrs[0][1] == recPackage[8]) &&
                    (recPackage[9] != cmd_rts) && (recPackage[9] != cmd_cts)){
                //Verifica se o endereço de destino confere com o endereço MAC
                //local, ou seja, "é ednereçado a mim" e se o endereço de origem
                //é diferente do número MAC local, ou seja, "não foi enviado por
                //mim". Só trata o pacote se as duas condições forem verdadeiras.
                // e confere tambem se o pacote foi enviado pelo mesmo enderço que enviou o rts

                //LOG dout << "MAC: correct crc. Propagate packet to APP layer." << std::endl;
                //LOG printf("Pacote recebido - ID: %u - Endereco de origem: %u%u\n", (unsigned char)recPackage[2],
                        //(unsigned char)recPackage[7], (unsigned char)recPackage[8]);
                d_num_packets_received++;
                pmt::pmt_t mac_payload = pmt::make_blob((char*) pmt::blob_data(blob) + 9, data_len - 9 - 2);
                message_port_pub(pmt::mp("app out"), pmt::cons(pmt::PMT_NIL, mac_payload));

                sendAck(recPackage);
            }
            else if(addr_bc_1 == recPackage[5] && addr_bc_2 == recPackage[6] && recPackage[9] == cmd_realignment){
                // Transmição Broadcast do canal de controle
                // Ver a frequencia para qual deve se mudar
                dout<<"Transmição Broadcast\n"<< std::endl;
            }
            else{
                //LOG printf("Pacote dropado. Mesmo endereço\n\n");
            }
        }
    }
    /**
     * Só envia pacote ack se a mensagem recebida não for de broadcast
     */
    bool sendAck(char* recPackage){
        char dAck[5];
        if(addr_bc_1 != recPackage[5] || addr_bc_2 != recPackage[6]){
            generateAck(recPackage, dAck);
            pmt::pmt_t packAck = pmt::cons(pmt::PMT_NIL, pmt::make_blob(dAck, 5));
            SendPackage* packageAck = new SendPackage(packAck, recPackage[2], true);
            send(packageAck);
        }
    }

    bool isAckPack(char* recPack) {
        bool isA = recPack[0] == 0x40;
        return isA;
    }

    /**
     * Marca o pacote como confirmado e diz que ele pode ser removido. Não
     * remove o pacote da fila diretamente para evitar problemas de
     * produtor/consumidor.
     */
    void removePackAcked(char* ackPack) {
        unsigned char packId;
        packId = ackPack[2];

        std::list<SendPackage*>::iterator it = sendList.begin();
        while (it != sendList.end()) {
            if ((*it)->getId() == packId) {
                (*it)->setCanRemove(true);
                lastPackAckedOrTimeToResendFinished = true;
                cond2.notify_all();
                printf("Package %u acked.\n\n", (unsigned char)ackPack[2]);
                break;
            }
            it++;
        }
    }

    /**
     * Função que trata a entrada da conexção "app in".
     */
    void app_in(pmt::pmt_t msg) {
        pmt::pmt_t blob;
        if(pmt::is_eof_object(msg) && conection_state == true){
            finish_communication();
            return;
        } else if (pmt::is_blob(msg)) {
            blob = msg;
        } else if (pmt::is_pair(msg)) {
            blob = pmt::cdr(msg);
        } else {
            dout << "MAC: unknown input" << std::endl;
            return;
        }
        //LOG printf("Preparando pacote para o endereco: %u%u\n\n", addr0[0], addr0[1]);
        if(!conection_state && !rts_send){
            start_communication();
            rts_send = true;
        }
        //Neste caso, todos os pacotes estão sendo enviados para o endereço
        //addr0, para melhorar os testes, este endereço poderia ser escolhido
        //aleatoriamente entre os endereços disponíveis.
        generate_mac((const char*) pmt::blob_data(blob), pmt::blob_length(blob), addr0);
        pmt::pmt_t pack = pmt::cons(pmt::PMT_NIL, pmt::make_blob(d_msg, d_msg_len));
        SendPackage* package = new SendPackage(pack, d_msg[2], false);
        package->setTime(0);
        send(package);
    }

    /*Esta funçao faz o envio do pacote de comando */
    void start_communication(){
        char* request = (char*)malloc(sizeof(char)*1);
        char packRequest[256];
        addr0[0] = 0x40;                                                                      // fazer atribuição do endereço via interface
        addr0[1] = 0xe8;
        generate_and_send_cmd(request, 0, packRequest, addr0, cmd_rts);
        dout<<"Sending RTS\n"<< std::endl;
    }

    void finish_communication(){
        char* request = (char*)malloc(sizeof(char)*1);
        char packRequest[256];
        generate_and_send_cmd(request, 0, packRequest, addr0, cmd_end_communication);

        addrs[0][0]=0x00;                                                                               //atualiza lista de endereço
        addrs[0][1]=0x00;
        dout<<"Sending end of communication\n"<< std::endl;
        dout << "MAC: exiting" << std::endl;
        //detail().get()->set_done(true);
    }

    void generate_and_send_cmd(char *buf, int len, char * c_msg, char* addr_dest, char command){
        generate_command(buf, len, c_msg, addr_dest, command);
        pmt::pmt_t packcmd = pmt::cons(pmt::PMT_NIL, pmt::make_blob(c_msg, c_msg_len));
        SendPackage* packagecmd = new SendPackage(packcmd, c_msg[2], false);
        packagecmd->setIsCmd(true);
        packagecmd->setTime(0);
        send(packagecmd);
    }

    /**Esta função inicia o processo de envio da mensagem. Ela coloca o pacote
     * na fila para envio, notifica a thread principal que há dados prontos para
     * serem enviados.
     * A função que implementa essa espera é a executeM().    */
    void send(SendPackage* pack) {
        if (pack->hasAckPackage()) {
            sendAckPackage(pack);
        }
        else {
            sendList.push_back(pack);
        }
        data_ready = true;
        cond.notify_all();
    }
    /**
     * Envia confirmação dos pacotes recebidos. Diferente dos outros pacotes,
     * o ack não é colocado em fila de envio, é enviado diretamente.
     */
    void sendAckPackage(SendPackage* pack) {
        //LOG std::cout << "Waiting Sifs: " << sifs << std::endl;
        boost::posix_time::millisec workTime(sifs);
        boost::this_thread::sleep(workTime);
        message_port_pub(pmt::mp("pdu out"), pack->getPackage());
        //LOG printf("Enviando ack ID: %u\n\n", pack->getId());
    }
    /**
     * Esta função sobrescreve a função nativa do GNU Radio que ativa o bloco.
     * Foi necessário usá-la para iniciar a thread principal.
     */
    bool start() {
        //Cria a thread principal de gerenciamento. Esta thread é criada para
        //evitar usar a thread (realmente) principal do bloco. Durante a
        //execução ela precisa ser pausada e retomada várias vezes, quando
        //fazemos isso com a thread do bloco, ela interrompe outras operações
        //como o carrier sense que é feito na função cs_in().
        exec = boost::shared_ptr<gr::thread::thread>
                (new gr::thread::thread(boost::bind(&mac_impl::executeM, this)));

        //Estes endereços estão sendo alocados dinamicamente.
        //no momento do recebimento do RTS
        //e no momento de enviar a primeira mensagem, há necessidade de se fazer via interface
        //apenas addrs[0]

        addr0[0] = 0x00;
        addr0[1] = 0x00;

        addr1[0] = 0x00;
        addr1[1] = 0x00;

        addr2[0] = 0x00;
        addr2[1] = 0x00;

        addrs[0] = addr0;
        addrs[1] = addr1;
        addrs[2] = addr2;

        return block::start();
    }
    /**
     * Esta função sobrescreve a função nativa do GNU Radio que ativa o bloco.
     * ela garante que a thread principal será fechada apenas quando o bloco for
     * desativado.
     */
    bool stop() {
        exec->interrupt();
        exec->join();
        return block::stop();
    }

    bool canExecute() {
        return data_ready;
    }

    /**
     * Função chamada pela thread principal, a partir da qual to.do o
     * gerenciamento acontece. Ela espera que os dados fiquem prontos, quando é
     * notificada de que há dados a enviar, envia todos os dados e volta ao
     * modo de espera.
     *
     * A função que faz notificação de dados prontos é a função send().
     */
    void executeM() {
        boost::unique_lock<boost::mutex> lock(mut);
        while (true) {
            while (!data_ready) {
                std::cout << "Loop" << std::endl;
                cond.wait(lock);
            }
            //Essa atribuição é necessária nesse ponto para evitar que dados
            //fiquem perdidos na fila por problemas de sincronização. Essa
            //variável é usada também pela função send() para notificar se há
            //dados a serem enviados.
            data_ready = false;
            runSending();
        }
    }

    /**
     * Envia de fato os pacotes e incrementa o número de reenvios.
     */
    bool sendPackageNow(SendPackage* pack) {
        pmt::pmt_t pmt_pack = pack->getPackage();
        struct timeval now;
        message_port_pub(pmt::mp("pdu out"), pmt_pack);
        lastPackAckedOrTimeToResendFinished = false;
        printf("Enviou pacote %u\n", pack->getId());
        gettimeofday(&now, NULL);
        pack->setTime((now.tv_sec * 1000) + (now.tv_usec / 1000)); // TEMPO DE REENVIO DO PROTOCOLO
        pack->increaseResends(max_retr);
        return true;
    }

    /**
     * Funçao que gerencia toso as operações enquanto houver dados para serem enviados.
     */
    bool runSending() {
        while (!sendList.empty()) {
            std::list<SendPackage*>::iterator it = sendList.begin();
            while ((it != sendList.end() && conection_state == true) || (it != sendList.end() && (*it) -> getIsCmd())) {
                //Remove os pacotes confirmados e que escederam a quantidade de reenvios
                if ((*it)->getCanRemove()) {
                    SendPackage* packToRemove = *it;
                    it++;
                    sendList.remove(packToRemove);
                    cw_current_backoff = cw_backoff_min;
                }
                else {
                    //LOG std::cout << "Waiting Diff: " << difs << std::endl;
                    boost::posix_time::millisec workTimeDifs(difs);
                    boost::this_thread::sleep(workTimeDifs);

                    if((*it)->getResends() > 0){
                        cw_current_backoff = cw_current_backoff * 2;
                    }

                    real_backoff = (std::rand() % cw_current_backoff) + 1;
                    boost::posix_time::millisec workTime(slotSize);

                    //tratamento do backoff
                    while(real_backoff >= 0){
                        boost::this_thread::sleep(workTime);
                        if(!isChannelBusy(referenceValueChannelBusy)){
                            real_backoff = real_backoff - slotSize;
                            //LOG std::cout << "Real backoff: " << real_backoff << std::endl;
                        }
                    }

                    sendPackageNow(*it);
                    //epera para reenvio
                    waitSending = boost::shared_ptr<gr::thread::thread>
                            (new gr::thread::thread(boost::bind(&mac_impl::waitResendingTime, this)));

                    boost::unique_lock<boost::mutex> lock2(mut2);
                    // a variável lastPackAckedOrTimeToResendFinished é manipulada em duas funções diferentes para garantir que
                    //essa espera durará até o recebimento da confirmação do pacote ou até o fim do tempo de espera para reenvio, o
                    //que acontecer primeiro.
                    while (!lastPackAckedOrTimeToResendFinished) {
                        cond2.wait(lock2);
                    }
                    waitSending->interrupt();
                    waitSending->join();
                }
            }
        }
        return true;
    }

    /**
     * Função que faz a espera para reenvio.
     */
    void waitResendingTime(){
        boost::posix_time::millisec workTimeResend(resend_waiting);
                    boost::this_thread::sleep(workTimeResend);

        lastPackAckedOrTimeToResendFinished = true;
        cond2.notify_all();
    }

    /**
     * Faz o carrier sense.
     * Com intervalo de tempo definido no parêmetro do bloco gráfico de
     * eventstream, faz a leitura do ambiente, verificando qual a potência do
     * sinal em uma certa frequência definida. Guarda esse valor em uma variável
     * que será usada internamente para decisões de canal livre ou ocupado.
     *
     * É importante ter atenção ao manipular threads nesse arquivo, pois
     * frequentemente quando se interrompe uma thread, um efeito colateral é
     * interromper a execução dessa função.
     */
    void cs_in(pmt::pmt_t msg) {
        pmt::pmt_t blob;

        if (pmt::is_blob(msg)) {
            blob = msg;
        } else if (pmt::is_pair(msg)) {
            blob = pmt::car(msg);
            //LOG std::cout << "Is pair" << std::endl;
        }

        float avPowerChannel = 0;
        float power = 0;

        //In this case, the blob is a dictionary, we are getting the value of power using the key "power"
        pmt::pmt_t pmtPower = pmt::dict_ref(blob, pmt::string_to_symbol("power"), pmt::get_PMT_NIL());
        power = pmt::to_float(pmtPower);

        //LOG std::cout << "Power: ";

        //LOG std::cout << power << std::endl;

        avPowerChannel = power;

        lastAvPower = avPowerChannel;
    }

    /**
     * Usa o valor de referência para determinar se o canal está livre.
     */
    bool isChannelBusy(float refValue) {
        return (lastAvPower > refValue);
    }

    /**
     * Função da implementação original. Funciona bem, mas tem um problema de
     * retorno, quando o crc falha, retorna true, no caso de sucesso, retorna
     * false.
     * @param buf
     * @param len
     * @return
     */
    uint16_t crc16(char *buf, int len) {
        uint16_t crc = 0;

        for (int i = 0; i < len; i++) {
            for (int k = 0; k < 8; k++) {
                int input_bit = (!!(buf[i] & (1 << k)) ^ (crc & 1));
                crc = crc >> 1;
                if (input_bit) {
                    crc ^= (1 << 15);
                    crc ^= (1 << 10);
                    crc ^= (1 << 3);
                }
            }
        }
        return crc;
    }

    /**
     * Gera os pacotes de confirmação. Implementada por mim, está em acordo com
     * o 802.15.4.
     * @param buf Usado apenas para verificação do id do pacote
     * @param dAck o pacote ack a ser configurado
     * @return Retorna o pacote ack configurado
     */
    char* generateAck(const char *buf, char* dAck) {
        unsigned char packId;
        packId = (unsigned char)buf[2];

        // ack frame: type 010
        dAck[0] = 0x40;
        dAck[1] = 0x00;

        // seq nr
        dAck[2] = packId;

        uint16_t crc = crc16(dAck, 3);

        dAck[3] = crc & 0xFF;
        dAck[4] = crc >> 8;

        return dAck;
    }


    /**
     * Gera os pacotes de comandos de comunicação.
     * @return Retorna o pacote comando configurado
     */
    void generate_command(char *buf, int len, char * c_msg, char* addr_dest, char command) {

        // SRC frame: type 011
        c_msg[0] = 0x60;//22 mac_TDMA
        c_msg[1] = 0x22;

        // sequencia number
        c_msg[2] = c_seq_nr++;

        // addr info
        c_msg[3] = 0xcd;
        c_msg[4] = 0xab;
        c_msg[5] = addr_dest[0];
        c_msg[6] = addr_dest[1];
        c_msg[7] = mac_addr_1;
        c_msg[8] = mac_addr_2;

        //comand filter
        c_msg[9] = command;

        //dout << buf<<" buf" << std::endl;

        std::memcpy(c_msg + 10, buf, len);

        uint16_t crc_cmd = crc16(c_msg, len + 10);

        c_msg[ 10 + len] = crc_cmd & 0xFF;
        c_msg[11 + len] = crc_cmd >> 8;

        c_msg_len = 10 + len + 2;
    }

    /**
     * Gera os pacotes de dados.
     * Essa função é da implementação original, melhorei ela um pouco,
     * mas precisa ser muito melhorada ainda. Os autores dizem que o pacote
     * está em acordo com o padrão 802.15.4. Confiei neles, conferi
     * tudo exceto o subfild de controle.
     */
    void generate_mac(const char *buf, int len, char* addr_dest) {

        // FCF
        // data frame, no security
        d_msg[0] = 0x41;
        d_msg[1] = 0x88;

        // seq nr
        d_msg[2] = d_seq_nr++;

        // addr info
        d_msg[3] = 0xcd;
        d_msg[4] = 0xab;
        d_msg[5] = addr_dest[0];
        d_msg[6] = addr_dest[1];
        d_msg[7] = mac_addr_1;
        d_msg[8] = mac_addr_2;

        std::memcpy(d_msg + 9, buf, len);

        uint16_t crc = crc16(d_msg, len + 9);

        d_msg[ 9 + len] = crc & 0xFF;
        d_msg[10 + len] = crc >> 8;

        d_msg_len = 9 + len + 2;
    }

    void print_message() {
        for (int i = 0; i < d_msg_len; i++) {
            dout << std::setfill('0') << std::setw(2) << std::hex << ((unsigned int) d_msg[i] & 0xFF) << std::dec << " ";
            if (i % 16 == 15) {
                dout << std::endl;
            }
        }
        dout << std::endl;
    }

    void print_c_message(char * c_msg) {
        for (int i = 0; i < c_msg_len; i++) {
            dout << std::setfill('0') << std::setw(2) << std::hex << ((unsigned int) c_msg[i] & 0xFF) << std::dec << " ";
            if (i % 16 == 15) {
                dout << std::endl;
            }
        }
        dout << std::endl;
    }

    int get_num_packet_errors() {
        return d_num_packet_errors;
    }

    int get_num_packets_received() {
        return d_num_packets_received;
    }

    float get_packet_error_ratio() {
        return float(d_num_packet_errors) / d_num_packets_received;
    }

private:
    // variaveis pacote de dados
    bool d_debug;
    int d_msg_offset;
    int d_msg_len;
    uint8_t d_seq_nr = 0;
    char d_msg[256]; // tamanho maximo da mensagem
    int d_num_packet_errors;
    int d_num_packets_received;
    // variaveis pacote de comando
    int c_msg_len;
    uint8_t c_seq_nr = 0;
    int connection_attempts=0;
};

mac::sptr
mac::make(bool debug) {
    return gnuradio::get_initial_sptr(new mac_impl(debug));
}
