type 'a coq_sig =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a sig2 =
  'a
  (* singleton inductive, whose constructor was exist2 *)

type ('a, 'p) sigT =
| Coq_existT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| Coq_existT (a, p) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| Coq_existT (x0, h) -> h

type 'a coq_Exc = 'a option

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

