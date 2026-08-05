(*  Title:      HOL/HOLCF/IOA/ABP/Check.ML
    Author:     Olaf Müller

The Model Checker.
*)

structure Check =
struct
 
(* ----------------------------------------------------------------
       P r o t o t y p e   M o d e l   C h e c k e r 
   ----------------------------------------------------------------*)

fun check(extacts,intacts,string_of_a,startsI,string_of_s,
          nexts,hom,transA,startsS) =
  let fun check_s(s,unchecked,checked) =
        let fun check_sa a unchecked =
              let fun check_sas t unchecked =
                    (if member (op =) extacts a then
                          (if transA(hom s,a,hom t) then ( )
                           else
                            error (cat_lines
                              ["Mapping of Externals!", string_of_s s, string_of_a a, string_of_s t]))
                     else (if hom(s)=hom(t) then ()
                           else
                            error (cat_lines
                              ["Error: Mapping of Internals!", string_of_s s, string_of_a a, string_of_s t]));
                     if member (op =) checked t then unchecked else insert (op =) t unchecked)
              in fold check_sas (nexts s a) unchecked end;
              val unchecked' = fold check_sa (extacts @ intacts) unchecked
        in    (if member (op =) startsI s then 
                    (if member (op =) startsS (hom s) then ()
                     else error "At start states!")
               else ();  
               checks(unchecked',s::checked)) end
      and checks([],_) = ()
        | checks(s::unchecked,checked) = check_s(s,unchecked,checked)
  in checks(startsI,[]) end;


(* ------------------------------------------------------
                 A B P     E x a m p l e
   -------------------------------------------------------*)

datatype msg = m | n | l;
datatype act = Next | S_msg of msg | R_msg of msg
                    | S_pkt of bool * msg | R_pkt of bool * msg
                    | S_ack of bool | R_ack of bool;

(* -------------------- Transition relation of Specification -----------*)

fun transA((u,s),a,(v,t)) = 
    (case a of 
       Next       => v andalso t = s |                         
       S_msg(q)   => u andalso not(v) andalso t = s@[q]   |    
       R_msg(q)   => u = v andalso s = (q::t)  |                    
       S_pkt(b,q) => false |                    
       R_pkt(b,q) => false |                    
       S_ack(b)   => false |                      
       R_ack(b)   => false);


(* ---------------------- Abstraction function --------------------------*)

fun hom((env,p,a,q,b,_,_)) = (env,q@(if (a=b) then tl(p) else p));


(* --------------------- Transition relation of Implementation ----------*)

fun nexts (s as (env,p,a,q,b,ch1,ch2)) action =
    (case action of
       Next       => if p=[] then [(true,p,a,q,b,ch1,ch2)] else [] |                         
       S_msg(mornorl)   => if env then [(false,p@[mornorl],a,q,b,ch1,ch2)] else [] |     
       R_msg(mornorl)   => if (q<>[] andalso mornorl=hd(q)) 
                        then [(env,p,a,tl(q),b,ch1,ch2)]
                        else [] |                    
       S_pkt(h,mornorl) => if (p<>[] andalso mornorl=hd(p) andalso h=a)
                        then (if (ch1<>[] andalso hd(rev(ch1))=(h,mornorl))
                              then [s]
                              else [s,(env,p,a,q,b,ch1@[(h,mornorl)],ch2)])
                        else [] |
       R_pkt(h,mornorl) => if (ch1<>[] andalso hd(ch1)=(h,mornorl))
                         then (if (h<>b andalso q=[])
                               then [(env,p,a,q@[mornorl],not(b),ch1,ch2),
                                     (env,p,a,q@[mornorl],not(b),tl(ch1),ch2)]
                               else [s,(env,p,a,q,b,tl(ch1),ch2)])
                          else [] | 
       S_ack(h)   => if (h=b)
                        then (if (ch2<>[] andalso h=hd(rev(ch2))) 
                              then [s]
                              else [s,(env,p,a,q,b,ch1,ch2@[h])])
                        else []  |                      
       R_ack(h)   => if (ch2<>[] andalso hd(ch2)=h)
                        then (if h=a
                              then [(env,tl(p),not(a),q,b,ch1,ch2),
                                    (env,tl(p),not(a),q,b,ch1,tl(ch2))]
                              else [s,(env,p,a,q,b,ch1,tl(ch2))]) 
                         else [])


val extactions = [Next,S_msg(m),R_msg(m),S_msg(n),R_msg(n),S_msg(l),R_msg(l)];
val intactions = [S_pkt(true,m),R_pkt(true,m),S_ack(true),R_ack(true),
                  S_pkt(false,m),R_pkt(false,m),S_ack(false),R_ack(false),
                  S_pkt(true,n),R_pkt(true,n),S_pkt(true,l),R_pkt(true,l),
               S_pkt(false,n),R_pkt(false,n),S_pkt(false,l),R_pkt(false,l)];


(* ------------------------------------
           Input / Output utilities 
   ------------------------------------*)

fun print_list (lpar, rpar, pre: 'a -> Buffer.T -> Buffer.T) (lll : 'a list) =
  let fun prec x = Buffer.add "," #> pre x
  in
    (case lll of
      [] => Buffer.add lpar #> Buffer.add rpar
    | x::lll => Buffer.add lpar #> pre x #> fold prec lll #> Buffer.add rpar)
   end;

fun pr_bool true = Buffer.add "true"
|   pr_bool false = Buffer.add "false";

fun pr_msg m = Buffer.add "m"
|   pr_msg n = Buffer.add "n"
|   pr_msg l = Buffer.add "l";

fun pr_act a = Buffer.add (case a of
      Next => "Next"|                         
      S_msg(ma) => "S_msg(ma)"  |
      R_msg(ma) => "R_msg(ma)"  |
      S_pkt(b,ma) => "S_pkt(b,ma)" |                    
      R_pkt(b,ma) => "R_pkt(b,ma)" |                    
      S_ack(b)   => "S_ack(b)" |                      
      R_ack(b)   => "R_ack(b)");

fun pr_pkt (b,ma) = Buffer.add "<" #> pr_bool b #> Buffer.add ", " #> pr_msg ma #> Buffer.add ">";

val pr_bool_list  = print_list("[","]",pr_bool);
val pr_msg_list   = print_list("[","]",pr_msg);
val pr_pkt_list   = print_list("[","]",pr_pkt);

fun pr_tuple (env,p,a,q,b,ch1,ch2) = 
  Buffer.add "{" #> pr_bool env #> Buffer.add ", " #> pr_msg_list p #> Buffer.add ", " #>
  pr_bool a #> Buffer.add ", " #> pr_msg_list q #> Buffer.add ", " #>
  pr_bool b #> Buffer.add ", " #> pr_pkt_list ch1 #> Buffer.add ", " #>
  pr_bool_list ch2 #> Buffer.add "}";

val content = Buffer.content o Buffer.build;

end;
