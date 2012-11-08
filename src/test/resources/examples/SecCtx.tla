------------------------------- MODULE SecCtx -------------------------------
EXTENDS Naturals, Integers, Relations
CONSTANTS usr_lst_cnt, REG_USR, INT, NAT
ASSUME usr_lst_cnt \in Nat\{0} /\ REG_USR = 0..(usr_lst_cnt-1)

min(S) == CHOOSE x \in S : \A i \in S: x \leq i

VARIABLES
    flg_comm_active,            (* communicating *)
    flg_got_cli_nonce,          (* Client Nonce received *)
    flg_sent_serv_nonce,        (* Server Nonce sent *)
    flg_sent_cert,              (* Server certificate sent *)
    flg_got_premaster,          (* premaster secret received from client *)
    flg_set_cmn_key,            (* session common key set *)
    flg_done_hs_verify,         (* Data for verifying a Handshake message checked *)
    flg_sent_hs_verify,         (* Data for verifying a Handshake message sent *)
    flg_cipher_on,              (* Applied encryption to communication data *)
    
    flg_allow_user_auth,        (* the propriety user authenticating user *)
    flg_done_user_auth,         (* user authenticated flag *)
    flg_allow_user_data,        (* the propriety sending and receiving user data flag *)
    
    flg_tx_msg_encoded,         (* encryption of sending data flag *)
    flg_tx_add_mac,             (* Given MAC  of sending data flag *)
    flg_allow_send_data,        (* Permission of sending TCP data flag*)
    
    flg_rx_msg_decoded,         (* encryption of receiviing data flag *)
    flg_rx_chk_mac,             (* Given MAC  of receiviing data flag *)
    flg_allow_recv_data,        (* Permission of giving application software received data flag*)
    
    auth_fail_cnt,              (* consecutive unsuccessful authentication attempts for each user *)
    recent_auth_tim             (* previous time of authentication attempts for each user for each user *)

Inv == (* Definition of type *)
    (* -------------------------------------------------------- *)
    flg_comm_active \in BOOLEAN /\
    flg_got_cli_nonce \in BOOLEAN /\
    flg_sent_serv_nonce \in BOOLEAN /\
    flg_sent_cert \in BOOLEAN /\
    flg_got_premaster \in BOOLEAN /\
    flg_set_cmn_key \in BOOLEAN /\
    flg_done_hs_verify \in BOOLEAN /\
    flg_sent_hs_verify \in BOOLEAN /\
    flg_cipher_on \in BOOLEAN /\
    
    flg_allow_user_auth \in BOOLEAN /\
    flg_done_user_auth \in BOOLEAN /\
    flg_allow_user_data \in BOOLEAN /\
    
    flg_tx_msg_encoded \in BOOLEAN /\
    flg_tx_add_mac \in BOOLEAN /\
    flg_allow_send_data \in BOOLEAN /\
    
    flg_rx_msg_decoded \in BOOLEAN /\
    flg_rx_chk_mac \in BOOLEAN /\
    flg_allow_recv_data \in BOOLEAN /\
    
    is_total_func(auth_fail_cnt, REG_USR, NAT) /\ (*   auth_fail_cnt : REG_USR +-> NAT & dom(auth_fail_cnt)=REG_USR &*)
    is_total_func(recent_auth_tim, REG_USR, INT) /\ (*recent_auth_tim : REG_USR +-> INT & dom(recent_auth_tim)=REG_USR &*)
    
    (flg_sent_serv_nonce=TRUE => flg_got_cli_nonce=TRUE) /\
    (flg_sent_cert=TRUE => flg_sent_serv_nonce=TRUE) /\
    (flg_got_premaster=TRUE => flg_sent_cert=TRUE) /\
    (flg_sent_hs_verify=TRUE => flg_got_premaster=TRUE) /\
    (flg_allow_user_auth = TRUE
        => (flg_sent_cert = TRUE) /\ (flg_got_premaster=TRUE) /\ (flg_sent_hs_verify=TRUE))
    
   /\     (flg_allow_user_data = TRUE
        => (flg_sent_cert = TRUE) /\ (flg_got_premaster=TRUE) /\ (flg_sent_hs_verify=TRUE))
  
  /\      
        (* Encryption of user data：Prevent eavesdropping *)
    ( flg_cipher_on=TRUE => flg_set_cmn_key=TRUE) /\ 
    ( flg_allow_user_auth=TRUE => flg_cipher_on=TRUE) /\
    ( flg_done_user_auth=TRUE => flg_allow_user_auth=TRUE) /\
    ( flg_allow_send_data=TRUE => (flg_allow_user_data=TRUE)/\(flg_tx_msg_encoded=TRUE) ) /\ 
    ( flg_allow_recv_data=TRUE => (flg_allow_user_data=TRUE)/\(flg_rx_msg_decoded=TRUE) ) /\    
        
        
        (* Make the unique common key for every session：Prevent replying *)
    ( flg_allow_user_auth=TRUE => flg_done_hs_verify=TRUE ) /\
    ( flg_allow_user_auth=TRUE => flg_sent_hs_verify=TRUE ) /\
    ( flg_cipher_on=TRUE => flg_got_cli_nonce=TRUE ) /\
    ( flg_cipher_on=TRUE => flg_sent_serv_nonce=TRUE ) /\
    ( flg_comm_active=FALSE => flg_set_cmn_key=FALSE) /\
    
    (* Make hash：Prevent Prevent falsifying(contain adding messages, 
    deleting messages and replacing an order of a message ) and replying *)
    ( flg_allow_send_data=TRUE => (flg_allow_user_data=TRUE)/\(flg_tx_add_mac=TRUE) ) /\ 
    ( flg_allow_recv_data=TRUE => (flg_allow_user_data=TRUE)/\(flg_rx_chk_mac=TRUE) ) /\
    
    (* Authenticate User：Prevent masquerading as an user *)
    ( flg_allow_user_auth = TRUE => flg_cipher_on = TRUE ) /\
    ( flg_allow_user_data = TRUE => flg_done_user_auth = TRUE )
       
        
SecCtx_Init ==
    flg_comm_active = FALSE /\
    flg_got_cli_nonce = FALSE /\
    flg_sent_serv_nonce = FALSE /\
    flg_sent_cert = FALSE /\
    flg_got_premaster = FALSE /\
    flg_set_cmn_key = FALSE /\
    flg_done_hs_verify = FALSE /\
    flg_sent_hs_verify = FALSE /\
    flg_cipher_on = FALSE /\
    flg_allow_user_auth = FALSE /\
    flg_done_user_auth = FALSE /\
    flg_allow_user_data = FALSE /\
    
    flg_tx_msg_encoded = FALSE /\
    flg_tx_add_mac = FALSE /\
    flg_allow_send_data = FALSE /\
    
    flg_rx_msg_decoded = FALSE /\
    flg_rx_chk_mac = FALSE /\
    flg_allow_recv_data = FALSE /\
    
    auth_fail_cnt = REG_USR \times {0} /\
    recent_auth_tim = (REG_USR \times {-1})
        
        
        
            (* Set flag operations *)
SetFlgCommActive == 
        /\ flg_comm_active = FALSE
        /\ flg_comm_active' = TRUE
        /\ UNCHANGED << flg_got_cli_nonce,flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key, flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth, flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded, flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim >>
        
SetFlgGotCliNonce == 
        /\ flg_got_cli_nonce' = TRUE        
        /\ UNCHANGED <<flg_comm_active, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
SetFlgSentServNonce == 
        /\ flg_got_cli_nonce = TRUE
        /\ flg_sent_serv_nonce' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
                
SetFlgSentCert ==
        /\ flg_sent_serv_nonce = TRUE
        /\ flg_sent_cert' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
                
SetFlgGotPremaster  == 
        /\ flg_sent_cert = TRUE
        /\ flg_got_premaster' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
        
SetFlgCmnKey ==
        /\ (flg_comm_active = TRUE)
        /\ (flg_got_premaster = TRUE)
        /\ (flg_got_cli_nonce = TRUE)
        /\ (flg_sent_serv_nonce = TRUE)
        /\ flg_set_cmn_key' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
    
SetFlgCipherOn == 
        /\ (flg_got_premaster = TRUE)
        /\ (flg_got_cli_nonce = TRUE)
        /\ (flg_sent_serv_nonce = TRUE)
        /\ (flg_set_cmn_key = TRUE)
        /\ flg_cipher_on' = TRUE 
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
                   
        
SetFlgDoneHsVerify  ==
        /\ flg_done_hs_verify' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
        
        
SetFlgSentHsVerify == 
        /\ flg_got_premaster = TRUE
        /\ flg_sent_hs_verify' = TRUE 
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
        
        
SetFlgAllowUserAuth == 
        /\ (flg_cipher_on = TRUE)
        /\ (flg_done_hs_verify = TRUE)
        /\ (flg_sent_hs_verify = TRUE)
        /\ flg_allow_user_auth' = TRUE 
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
        
SetFlgDoneUserAuth  == 
        /\  flg_allow_user_auth = TRUE
        /\ flg_done_user_auth' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    

        
SetSuccessUserAuth(usr, tim) ==
        /\ usr \in INT /\ usr \in REG_USR /\ tim \in INT
        /\    flg_allow_user_auth = TRUE
            
        /\  flg_done_user_auth' = TRUE
        /\  auth_fail_cnt'= relational_overriding(auth_fail_cnt, {<<usr,0>>}) 
        /\  recent_auth_tim' = relational_overriding(recent_auth_tim, {<<usr, tim>>})    
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data>>    
        
SetFailUserAuth(usr, tim) ==
        /\ usr \in INT /\ usr \in REG_USR /\ tim \in INT  
        /\    flg_done_user_auth' = FALSE
        /\    flg_allow_user_data' = FALSE 
        /\    flg_allow_send_data' = FALSE 
        /\    flg_allow_recv_data' = FALSE
        /\    auth_fail_cnt' = relational_overriding(auth_fail_cnt, {<<usr,min({relational_call(auth_fail_cnt,usr)+1, 3})>>})
        /\    recent_auth_tim' = relational_overriding(recent_auth_tim, {<<usr, tim>>})      
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth, flg_tx_msg_encoded,flg_tx_add_mac,flg_rx_msg_decoded,flg_rx_chk_mac>>    
        
 SetFlgAllowUserData == 
        /\  (flg_sent_cert = TRUE) 
        /\ (flg_got_premaster=TRUE)
        /\ (flg_sent_hs_verify = TRUE)
        /\ (flg_cipher_on = TRUE)
        /\ (flg_done_user_auth = TRUE)
        /\ flg_allow_user_data' = TRUE 
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
                
SetFlgTxMsgEncoded ==
        /\ flg_tx_msg_encoded' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
    
SetFlgTxAddMac  ==
        /\ flg_tx_add_mac' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
         
    
SetFlgAllowSendData == 
        /\ (flg_allow_user_data=TRUE)
        /\ (flg_tx_msg_encoded = TRUE)
        /\ (flg_tx_add_mac = TRUE)
        /\ flg_allow_send_data' = TRUE 
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
         

SetFlgRxMsgDecoded  ==
        /\ flg_rx_msg_decoded' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        

SetFlgRxChkMac  ==
        /\ flg_rx_chk_mac' = TRUE
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        


SetFlgAllowRecvData == 
        /\ flg_cipher_on = TRUE
        /\ (flg_allow_user_data = TRUE)
        /\ (flg_rx_msg_decoded = TRUE)
        /\ (flg_rx_chk_mac = TRUE)
        /\ flg_allow_recv_data' = TRUE 
        /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,auth_fail_cnt,recent_auth_tim>>    
        
    (* Complete Handshake  *)
SetFlgsHndshkCompleteSts == 
        flg_comm_active' = TRUE /\
        flg_got_cli_nonce' = TRUE /\
        flg_sent_serv_nonce' = TRUE /\
        flg_sent_cert' = TRUE /\
        flg_got_premaster' = TRUE /\
        flg_set_cmn_key' = TRUE /\
        flg_done_hs_verify' = TRUE /\
        flg_sent_hs_verify' = TRUE /\
        flg_cipher_on' = TRUE /\
        flg_allow_user_auth' = TRUE
        /\ UNCHANGED  <<flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
    (* Reset Handshake Status *)
ResetFlgsHndshkCompleteSts == 
    /\ flg_allow_user_data = FALSE
    
    /\  flg_comm_active' = FALSE /\
        flg_got_cli_nonce' = FALSE /\
        flg_sent_serv_nonce' = FALSE /\
        flg_sent_cert' = FALSE /\
        flg_got_premaster' = FALSE /\
        flg_set_cmn_key' = FALSE /\
        flg_done_hs_verify' = FALSE /\
        flg_sent_hs_verify' = FALSE /\
        flg_cipher_on' = FALSE /\
        flg_allow_user_auth' = FALSE /\
        flg_done_user_auth' =FALSE
    /\ UNCHANGED <<flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
    (* Complete user authentication *)
SetFlgsAuthCompleteSts ==
    /\ flg_allow_user_auth = TRUE
    /\
        flg_done_user_auth' = TRUE  /\
        flg_allow_user_data' = TRUE
    /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
    (* Reset user authentication status *)
ResetFlgsAuthCompleteSts == 
    /\
        flg_done_user_auth' = FALSE /\
        flg_allow_user_data' = FALSE /\
        
        flg_allow_send_data' = FALSE /\
        flg_allow_recv_data' = FALSE
    /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth, flg_tx_msg_encoded,flg_tx_add_mac,flg_rx_msg_decoded,flg_rx_chk_mac,auth_fail_cnt,recent_auth_tim>>    
          

    (* Complete https_acp successfully *)
SetFlgsAcpCompleteSts == 
    /\
        flg_comm_active' = TRUE /\
        flg_got_cli_nonce' = TRUE /\
        flg_sent_serv_nonce' = TRUE /\
        flg_sent_cert' = TRUE /\
        flg_got_premaster' = TRUE /\
        flg_set_cmn_key' = TRUE /\
        flg_done_hs_verify' = TRUE /\
        flg_sent_hs_verify' = TRUE /\
        flg_cipher_on' = TRUE /\
        flg_allow_user_auth' = TRUE /\
        flg_done_user_auth' = TRUE  /\
        flg_allow_user_data' = TRUE
    /\ UNCHANGED <<flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        

    (* Reset https_acp status *)
ResetFlgsAcpCompleteSts == 
    /\
        flg_comm_active' = FALSE /\
        flg_got_cli_nonce' = FALSE /\
        flg_sent_serv_nonce' = FALSE /\
        flg_sent_cert' = FALSE /\
        flg_got_premaster' = FALSE /\
        flg_set_cmn_key' = FALSE /\
        flg_done_hs_verify' = FALSE /\
        flg_sent_hs_verify' = FALSE /\
        flg_cipher_on' = FALSE /\
        flg_allow_user_auth' = FALSE /\
        flg_done_user_auth' = FALSE /\
        flg_allow_user_data' = FALSE /\
        
        flg_allow_send_data' = FALSE /\
        flg_allow_recv_data' = FALSE
    /\ UNCHANGED <<flg_tx_msg_encoded,flg_tx_add_mac,flg_rx_msg_decoded,flg_rx_chk_mac,auth_fail_cnt,recent_auth_tim>>    
        
(* Set status of user data receiving  *)
SetFlgRx == 
    /\ flg_allow_user_data = TRUE /\
        flg_allow_recv_data '= TRUE /\
        flg_rx_msg_decoded' = TRUE /\
        flg_rx_chk_mac' = TRUE
    /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,auth_fail_cnt,recent_auth_tim>>    
        
    
    
ResetFlgRx == 
    /\
        flg_allow_recv_data' = FALSE /\
        flg_rx_msg_decoded' = FALSE /\
        flg_rx_chk_mac' = FALSE
    /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,auth_fail_cnt,recent_auth_tim>>    
        
    
    (* Set status of user data transmitting  *)
SetFlgTx == 
    /\ flg_allow_user_data = TRUE /\
        flg_allow_send_data' = TRUE /\
        flg_tx_msg_encoded' = TRUE /\
        flg_tx_add_mac' = TRUE
    /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
        
ResetFlgTx == 
    /\
        flg_allow_send_data' = FALSE /\
        flg_tx_msg_encoded' = FALSE /\
        flg_tx_add_mac' = FALSE
    /\ UNCHANGED  <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
              
    
SetAuthInf(usr, tim, cnt) ==
    /\ usr \in INT /\ usr \in REG_USR /\ tim \in INT /\ cnt \in NAT
    /\
        auth_fail_cnt'= relational_overriding(auth_fail_cnt, {<<usr,cnt>>}) /\
        recent_auth_tim' = relational_overriding(recent_auth_tim, {<<usr, tim>>})  
    /\ UNCHANGED <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data>>    
            
        
(* set https_acp complete status and reset the count of unsuccessful authentication attemps *)
SetAuthSuccessSts(usr, cnt, tim) == 
    /\ usr \in INT /\ usr \in REG_USR /\ cnt \in NAT /\ tim \in INT
    /\
        flg_comm_active' = TRUE /\
        flg_got_cli_nonce' = TRUE /\
        flg_sent_serv_nonce' = TRUE /\
        flg_sent_cert' = TRUE /\
        flg_got_premaster' = TRUE /\
        flg_set_cmn_key' = TRUE /\
        flg_done_hs_verify' = TRUE /\
        flg_sent_hs_verify' = TRUE /\
        flg_cipher_on' = TRUE /\
        flg_allow_user_auth' = TRUE /\
        flg_done_user_auth' = TRUE  /\
        flg_allow_user_data' = TRUE /\
        
        auth_fail_cnt'= relational_overriding(auth_fail_cnt, {<<usr,cnt>>}) /\
        recent_auth_tim' = relational_overriding(recent_auth_tim, {<<usr, tim>>})   
    /\ UNCHANGED <<flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data>>    
                 
    (* Reset https_acp status and count up unsuccessful authentication attemps *)
SetAuthFailSts(usr, cnt, tim) == 
    /\ usr \in INT /\ usr \in REG_USR /\ cnt \in NAT /\ tim \in INT
    /\
        flg_comm_active' = FALSE /\
        flg_got_cli_nonce' = FALSE /\
        flg_sent_serv_nonce' = FALSE /\
        flg_sent_cert' = FALSE /\
        flg_got_premaster' = FALSE /\
        flg_set_cmn_key' = FALSE /\
        flg_done_hs_verify' = FALSE /\
        flg_sent_hs_verify' = FALSE /\
        flg_cipher_on' = FALSE /\
        flg_allow_user_auth' = FALSE /\
        flg_done_user_auth' = FALSE /\
        flg_allow_user_data' = FALSE /\
        
        flg_allow_send_data' = FALSE /\
        flg_allow_recv_data' = FALSE /\
        
        auth_fail_cnt'= relational_overriding(auth_fail_cnt, {<<usr,cnt>>}) /\
        recent_auth_tim' = relational_overriding(recent_auth_tim, {<<usr, tim>>})       
    /\ UNCHANGED <<flg_tx_msg_encoded,flg_tx_add_mac,flg_rx_msg_decoded,flg_rx_chk_mac>>    
                   
        
        
allVars == <<flg_comm_active, flg_got_cli_nonce, flg_sent_serv_nonce, flg_sent_cert,flg_got_premaster,flg_set_cmn_key,flg_done_hs_verify,flg_sent_hs_verify,flg_cipher_on, flg_allow_user_auth,flg_done_user_auth,flg_allow_user_data, flg_tx_msg_encoded,flg_tx_add_mac,flg_allow_send_data,flg_rx_msg_decoded,flg_rx_chk_mac,flg_allow_recv_data,auth_fail_cnt,recent_auth_tim>>    
             
             
              
SecCtx_Next == 
        \/ SetFlgCommActive    
        \/ SetFlgGotCliNonce
        \/ SetFlgSentServNonce
        \/ SetFlgSentCert
        \/ SetFlgGotPremaster
        \/ SetFlgCmnKey
        \/ SetFlgCipherOn
        \/ SetFlgDoneHsVerify
        \/ SetFlgSentHsVerify
        \/ SetFlgAllowUserAuth
        \/ SetFlgDoneUserAuth
        \/ \E usr \in REG_USR, tim \in INT: SetSuccessUserAuth(usr, tim)
        \/ \E usr \in REG_USR, tim \in INT: SetFailUserAuth(usr, tim)
        \/ SetFlgAllowUserData
        \/ SetFlgTxMsgEncoded
        \/ SetFlgTxAddMac
        \/ SetFlgAllowSendData
        \/ SetFlgRxMsgDecoded
        \/ SetFlgRxChkMac
        \/ SetFlgAllowRecvData
        \/ SetFlgsHndshkCompleteSts
        \/ ResetFlgsHndshkCompleteSts
        \/ SetFlgsAuthCompleteSts
        \/ SetFlgsAcpCompleteSts
        \/ ResetFlgsAcpCompleteSts
        \/ SetFlgRx
        \/ ResetFlgRx
        \/ SetFlgTx
        \/ ResetFlgTx
        \/ \E usr \in REG_USR, tim \in INT, cnt \in NAT: SetAuthInf(usr, tim, cnt)
        \/ \E usr \in REG_USR, tim \in INT, cnt \in NAT: SetAuthSuccessSts(usr, cnt, tim)
        \/ \E usr \in REG_USR, tim \in INT, cnt \in NAT: SetAuthFailSts(usr, cnt, tim)

=============================================================================
