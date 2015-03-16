type 'a coq_Stream = 'a __coq_Stream Lazy.t
and 'a __coq_Stream =
| Cons of 'a * 'a coq_Stream

val hd : 'a1 coq_Stream -> 'a1

val tl : 'a1 coq_Stream -> 'a1 coq_Stream

