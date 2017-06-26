 (* ProVerif for 2FLIP *)
param traceDisplay = long.
(* channels for publishing key and private communication *)
free c_pub.
private free c_UseriInputForReg.	(* private channel from Useri to TDi in reg *)
private free c_UseriInputForRun.	(* private channel from Useri to TDi in run *)
private free c_UserjInputForReg.	(* private channel from Userj to TDj in reg *)
private free c_UserjInputForRun.	(* private channel from Userj to TDj in run *)
private free c_Reg2TA.				(* private channel from TDs to CA in reg *)
private free c_TA2TDi.				(* private channel from CA to TD in reg *)
private free c_TA2TPDi.				(* private channel from CA to TPD in reg *)
private free c_TA2TDj.				(* private channel from CA to TD in reg *)
private free c_TA2TPDj.				(* private channel from CA to TPD in reg *)
private free c_ViTD2TPD.			(* private channel from TDi to TPDi *)
private free c_VjTD2TPD.			(* private channel from TDj to TPDj *)

(* Active adversary *)
param attacker = active.


(* Params in registration phase for vehicle i and j *)
data ID_CA/0.	(* identity of CA*)
data info_i/0.	(* registration information of Vehicle i*)
data info_j/0.	(* registration information of Vehicle j*)
data true/0.	(* true value*)





fun h/1.
fun XOR/2.
fun Enc/2.
fun Dec/2.
fun MAC/2.
fun Consume/1.
fun GenPubKey/2.
fun Sign/2.
fun Verify/3.

private fun genAlpha/0.


equation Dec(k, Enc(k,m)) = m.
equation Verify(k, m, Sign(m,k)) = true.
equation XOR(m1,m2) = XOR(m2, m1).
reduc DXOR(XOR(m1,m2),m2) = m1.
reduc DMAC(km,MAC(km,m))=m.

(* Test whether attacker can pass V2V authentication*)
(* query ev:endAuthTPDLogin(x1,x2,x3) ==> ev:beginAuthTPDLogin(x1,x2,x3).*)
(* Test whether attacker can pass TD 2 TPD authentication*)
(* query ev:endAuthRequest(x4,x5,x6,x7) ==> ev:beginAuthRequest(x4,x5,x6,x7). *)
(* Test whether attacker can pass TD 2 TPD authentication*)
(* query ev:endAuthMutual(x8,x9,x10,x11) ==> ev:beginAuthMutual(x8,x9,x10,x11). *)
(* Test whether attacker can acquire ID_i, ID_j, pw_iu, pw_ju *)
(* query attacker:(ID_i,ID_j,PID_i,PID_j,km). *)


(* Process for CA *)
let p_TA = 	new alpha;
			new km;
			new ts_km;
			new PID_i;
			new PID_j;
			new TDID_i;
			new TDID_j;

			let S_ID_CA = h(ID_CA) in
			let kp = GenPubKey(alpha,S_ID_CA) in
			out(c_pub,S_ID_CA);

			(* Registration for Veihcle i*)
			in(c_Reg2TA, reg_info_i);
			let (ID_i',gamma_iu,info_i') = reg_info_i in
			let pS_i = XOR(h((ID_i',TDID_i,PID_i)),h((TDID_i,km))) in
			let pU_iu = XOR(h((ID_i',gamma_iu,PID_i)),h((TDID_i,km))) in
			let pV_iu = h(XOR(gamma_iu,PID_i)) in
			let pK_iu= XOR(PID_i,h((TDID_i,gamma_iu))) in

			(* Registration for Veihcle j*)
			in(c_Reg2TA, reg_info_j);
			let (ID_j',gamma_ju,info_j') = reg_info_j in
			let pS_j = XOR(h((ID_j',TDID_j,PID_j)),h((TDID_j,km))) in
			let pU_ju = XOR(h((ID_j',gamma_ju,PID_j)),h((TDID_j,km))) in
			let pV_ju = h(XOR(gamma_ju,PID_j)) in
			let pK_ju= XOR(PID_j,h((TDID_j,gamma_ju))) in

			(* configure TDi and TPDi*)
			out(c_TA2TDi,(TDID_i,pS_i,pV_iu,pK_iu));
			out(c_TA2TPDi,(TDID_i,PID_i,km,pU_iu,ts_km,pK_iu));

			(* configure TDj and TPDj*)
			out(c_TA2TDj,(TDID_j,pS_j,pV_ju,pK_ju));
			out(c_TA2TPDj,(TDID_j,PID_j,km,pU_ju,ts_km,pK_ju)).

(* Process for User i *)
let p_Useri = new pw_iu;
			out(c_UseriInputForReg,pw_iu);  (* Input password for registration from User i *)
			(*-------------end of registration-------------*)
			out(c_UseriInputForRun,pw_iu).	(* Input password for run from User i *)

(* Process for User j *)
let p_Userj = new pw_ju;
			out(c_UserjInputForReg,pw_ju); 	(* Input password for registration from User j *)
			(*-------------end of registration-------------*)
			out(c_UserjInputForRun,pw_ju).	(* Input password for run from User j *)
			(*-------------end of login TDi-------------*)


(* Process for Telematics Device of Vehicle i *)
let p_TDi = new ID_i;
			new ts;

			in(c_UseriInputForReg,pw_iu);
			let gamma_iu = h(pw_iu) in
			out(c_Reg2TA,(ID_i,gamma_iu,info_i));
			in(c_TA2TDi,reg_td_i);
			let (TDID_i,pS_i,pV_iu,pK_iu) = reg_td_i in
			(*-------------end of registration-------------*)
			in(c_UseriInputForRun,pw_iu');
			let gamma_iu' = h(pw_iu') in
			let PID_i' = XOR (pK_iu, h((TDID_i,gamma_iu'))) in
			let pV_iu' = h(XOR(gamma_iu',PID_i')) in
			if pV_iu' = pV_iu then (* password verification *)
			(*-------------end of login TD -------------*)	

			
				let PID_i_ts = XOR(h((ID_i,TDID_i,PID_i')), h((PID_i',ts))) in
				let sigPID_i = h((pS_i,PID_i',ts)) in
				event beginAuthTPDLogin(PID_i_ts, sigPID_i, ts);(*query begin for TD 2 TPD authentication*)
				out(c_ViTD2TPD,(PID_i_ts, sigPID_i, ts)).
			(*-------------end of trying logining TPD-------------*)	

(* Process for Tamper Proof Device of Vehicle i *)
let p_TPDi = in(c_TA2TPDi, reg_tpd_i);
			let (TDID_i,PID_i,km,pU_iu,ts_km,pK_iu) = reg_tpd_i in
			(*-------------end of registration-------------*)
			in(c_ViTD2TPD, loginInfo_i);
			let (PID_i_ts, sigPID_i, ts) = loginInfo_i in
			let chi_i = DXOR(PID_i_ts, h((PID_i,ts))) in
			let sigPID_i'= h((XOR(chi_i,h((TDID_i,km))),PID_i,ts)) in
			if sigPID_i' = sigPID_i then
			(*-------------end of verification login message-------------*)
				new m;
				let sigMSG_i = MAC(km,(PID_i_ts,h((m,km)),ts)) in
				event endAuthTPDLogin(PID_i_ts, sigPID_i, ts);(*query end for TD 2 TPD authentication*)
				event beginAuthRequest(PID_i_ts, sigMSG_i, ts,m);(*query begin for V2V authentication*)
				out(c_pub, (PID_i_ts,sigMSG_i,ts,m));
				(*out(c_pub, (choice[PID_j_ts,r0],sigMSG_i,ts,m);*)

			(*-------------end of login TPD and broadcast messages-------------*)
			in(c_pub, message_j);
			let (PID_j_ts',sigMUT_j,ts_l,m_l) = message_j in
			let theta_i' = DXOR(sigMSG_i, h((m_l,km))) in
			let sigMUT_j' = MAC(km,(theta_i',h((m_l,km)),ts_l)) in
			if sigMUT_j' = sigMUT_j then
				let accesstoken = MAC(km,(PID_i_ts,h((m_l,km)),ts_l)) in
				event endAuthMutual(PID_j_ts',sigMUT_j,ts_l,m_l).(*query end for mutual message*)

(* Process for Telematics Device of Vehicle j *)
let p_TDj = new ID_j;
			in(c_UserjInputForReg,pw_ju);
			let gamma_ju = h(pw_ju) in
			out(c_Reg2TA,(ID_j,gamma_ju,info_j));
			in(c_TA2TDj,reg_td_j);
			let (TDID_j,pS_ju,pV_ju,pK_ju) = reg_td_j in 0.
			(*-------------end of registration-------------*)


(* Process for Tamper Proof Device of Vehicle j *)
let p_TPDj =
			new m_l;
			new ts_l;
			new PID_j_ts;

			in(c_TA2TPDj, reg_tpd_j);
			let (TDID_j,PID_j,km,pU_ju,ts_km,pK_ju) = reg_tpd_j in
			(*-------------end of registration-------------*)
			in(c_pub, message_i);
			let (PID_i_ts,sigMSG_i,ts,m) = message_i in
			let sigMSG_i' = MAC(km, (PID_i_ts, h((m, km)), ts)) in
			if sigMSG_i'= sigMSG_i then
		
			event endAuthRequest(PID_i_ts,sigMSG_i,ts,m);(*query end for V2V authentication*)
			(*-------------end of authentication-------------*)			
		
			let theta_i = DXOR(sigMSG_i', h((m_l,km))) in
			let sigMUT_j = MAC(km,(theta_i,h((m_l,km)),ts_l)) in
			event beginAuthMutual(PID_j_ts,sigMUT_j,ts_l,m_l);(*query begin for mutual message*)
			(* out(c_pub, (PID_j_ts,sigMUT_j,ts_l,m_l)). *)
			out(c_pub, (choice[PID_j_ts,r0],sigMUT_j,ts_l,m_l)). 
			
			

(* The Processes *)
process 
new r0;
!(p_Useri | p_Userj | p_TA | p_TDi | p_TDj | p_TPDi | p_TPDj)