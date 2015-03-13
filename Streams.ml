type 'a coq_Stream = 'a __coq_Stream Lazy.t
and 'a __coq_Stream =
| Cons of 'a * 'a coq_Stream

(** val hd : 'a1 coq_Stream -> 'a1 **)

let hd x =
  let Cons (a, s) = Lazy.force x in a

(** val tl : 'a1 coq_Stream -> 'a1 coq_Stream **)

let tl x =
  let Cons (a, s) = Lazy.force x in s

