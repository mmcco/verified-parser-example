type __ = Obj.t

type unit0 =
| Tt

type bool =
| True
| False

val implb : bool -> bool -> bool

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

val plus : nat -> nat -> nat

val max : nat -> nat -> nat

val min : nat -> nat -> nat

val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

val nat_compare : nat -> nat -> comparison

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

module type EqLtLe = 
 sig 
  type t 
 end

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> sumbool
 end

module type OrderedType' = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> sumbool
 end

module OT_to_Full : 
 functor (O:OrderedType') ->
 sig 
  type t = O.t
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> sumbool
 end

module MakeOrderTac : 
 functor (O:EqLtLe) ->
 functor (P:sig 
  
 end) ->
 sig 
  
 end

module OT_to_OrderTac : 
 functor (OT:OrderedType) ->
 sig 
  module OTF : 
   sig 
    type t = OT.t
    
    val compare : t -> t -> comparison
    
    val eq_dec : t -> t -> sumbool
   end
  
  module TO : 
   sig 
    type t = OTF.t
    
    val compare : t -> t -> comparison
    
    val eq_dec : t -> t -> sumbool
   end
 end

module OrderedTypeFacts : 
 functor (O:OrderedType') ->
 sig 
  module OrderTac : 
   sig 
    module OTF : 
     sig 
      type t = O.t
      
      val compare : t -> t -> comparison
      
      val eq_dec : t -> t -> sumbool
     end
    
    module TO : 
     sig 
      type t = OTF.t
      
      val compare : t -> t -> comparison
      
      val eq_dec : t -> t -> sumbool
     end
   end
  
  val eq_dec : O.t -> O.t -> sumbool
  
  val lt_dec : O.t -> O.t -> sumbool
  
  val eqb : O.t -> O.t -> bool
 end

module Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod
    -> (positive, mask) prod
  
  val sqrtrem : positive -> (positive, mask) prod
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod
  
  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
 end

module Coq_Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod
    -> (positive, mask) prod
  
  val sqrtrem : positive -> (positive, mask) prod
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod
  
  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
  
  val eq_dec : positive -> positive -> sumbool
  
  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  val coq_PeanoView_rect :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val coq_PeanoView_rec :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView : positive -> coq_PeanoView
  
  val coq_PeanoView_iter :
    'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1
  
  val eqb_spec : positive -> positive -> reflect
  
  val switch_Eq : comparison -> comparison -> comparison
  
  val mask2cmp : mask -> comparison
  
  val leb_spec0 : positive -> positive -> reflect
  
  val ltb_spec0 : positive -> positive -> reflect
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      'a1 -> 'a1 -> 'a1
    
    val max_dec : positive -> positive -> sumbool
    
    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      'a1 -> 'a1 -> 'a1
    
    val min_dec : positive -> positive -> sumbool
   end
  
  val max_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : positive -> positive -> sumbool
  
  val min_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : positive -> positive -> sumbool
 end

module N : 
 sig 
  type t = n
  
  val zero : n
  
  val one : n
  
  val two : n
  
  val succ_double : n -> n
  
  val double : n -> n
  
  val succ : n -> n
  
  val pred : n -> n
  
  val succ_pos : n -> positive
  
  val add : n -> n -> n
  
  val sub : n -> n -> n
  
  val mul : n -> n -> n
  
  val compare : n -> n -> comparison
  
  val eqb : n -> n -> bool
  
  val leb : n -> n -> bool
  
  val ltb : n -> n -> bool
  
  val min : n -> n -> n
  
  val max : n -> n -> n
  
  val div2 : n -> n
  
  val even : n -> bool
  
  val odd : n -> bool
  
  val pow : n -> n -> n
  
  val square : n -> n
  
  val log2 : n -> n
  
  val size : n -> n
  
  val size_nat : n -> nat
  
  val pos_div_eucl : positive -> n -> (n, n) prod
  
  val div_eucl : n -> n -> (n, n) prod
  
  val div : n -> n -> n
  
  val modulo : n -> n -> n
  
  val gcd : n -> n -> n
  
  val ggcd : n -> n -> (n, (n, n) prod) prod
  
  val sqrtrem : n -> (n, n) prod
  
  val sqrt : n -> n
  
  val coq_lor : n -> n -> n
  
  val coq_land : n -> n -> n
  
  val ldiff : n -> n -> n
  
  val coq_lxor : n -> n -> n
  
  val shiftl_nat : n -> nat -> n
  
  val shiftr_nat : n -> nat -> n
  
  val shiftl : n -> n -> n
  
  val shiftr : n -> n -> n
  
  val testbit_nat : n -> nat -> bool
  
  val testbit : n -> n -> bool
  
  val to_nat : n -> nat
  
  val of_nat : nat -> n
  
  val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val eq_dec : n -> n -> sumbool
  
  val discr : n -> positive sumor
  
  val binary_rect : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val binary_rec : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val leb_spec0 : n -> n -> reflect
  
  val ltb_spec0 : n -> n -> reflect
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  module Private_NZPow : 
   sig 
    
   end
  
  module Private_NZSqrt : 
   sig 
    
   end
  
  val sqrt_up : n -> n
  
  val log2_up : n -> n
  
  module Private_NZDiv : 
   sig 
    
   end
  
  val lcm : n -> n -> n
  
  val eqb_spec : n -> n -> reflect
  
  val b2n : bool -> n
  
  val setbit : n -> n -> n
  
  val clearbit : n -> n -> n
  
  val ones : n -> n
  
  val lnot : n -> n -> n
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : n -> n -> sumbool
    
    val min_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : n -> n -> sumbool
   end
  
  val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : n -> n -> sumbool
  
  val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : n -> n -> sumbool
 end

val rev : 'a1 list -> 'a1 list

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val rev' : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

module Z : 
 sig 
  type t = z
  
  val zero : z
  
  val one : z
  
  val two : z
  
  val double : z -> z
  
  val succ_double : z -> z
  
  val pred_double : z -> z
  
  val pos_sub : positive -> positive -> z
  
  val add : z -> z -> z
  
  val opp : z -> z
  
  val succ : z -> z
  
  val pred : z -> z
  
  val sub : z -> z -> z
  
  val mul : z -> z -> z
  
  val pow_pos : z -> positive -> z
  
  val pow : z -> z -> z
  
  val square : z -> z
  
  val compare : z -> z -> comparison
  
  val sgn : z -> z
  
  val leb : z -> z -> bool
  
  val ltb : z -> z -> bool
  
  val geb : z -> z -> bool
  
  val gtb : z -> z -> bool
  
  val eqb : z -> z -> bool
  
  val max : z -> z -> z
  
  val min : z -> z -> z
  
  val abs : z -> z
  
  val abs_nat : z -> nat
  
  val abs_N : z -> n
  
  val to_nat : z -> nat
  
  val to_N : z -> n
  
  val of_nat : nat -> z
  
  val of_N : n -> z
  
  val to_pos : z -> positive
  
  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pos_div_eucl : positive -> z -> (z, z) prod
  
  val div_eucl : z -> z -> (z, z) prod
  
  val div : z -> z -> z
  
  val modulo : z -> z -> z
  
  val quotrem : z -> z -> (z, z) prod
  
  val quot : z -> z -> z
  
  val rem : z -> z -> z
  
  val even : z -> bool
  
  val odd : z -> bool
  
  val div2 : z -> z
  
  val quot2 : z -> z
  
  val log2 : z -> z
  
  val sqrtrem : z -> (z, z) prod
  
  val sqrt : z -> z
  
  val gcd : z -> z -> z
  
  val ggcd : z -> z -> (z, (z, z) prod) prod
  
  val testbit : z -> z -> bool
  
  val shiftl : z -> z -> z
  
  val shiftr : z -> z -> z
  
  val coq_lor : z -> z -> z
  
  val coq_land : z -> z -> z
  
  val ldiff : z -> z -> z
  
  val coq_lxor : z -> z -> z
  
  val eq_dec : z -> z -> sumbool
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val leb_spec0 : z -> z -> reflect
  
  val ltb_spec0 : z -> z -> reflect
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  val sqrt_up : z -> z
  
  val log2_up : z -> z
  
  module Private_NZDiv : 
   sig 
    
   end
  
  module Private_Div : 
   sig 
    module Quot2Div : 
     sig 
      val div : z -> z -> z
      
      val modulo : z -> z -> z
     end
    
    module NZQuot : 
     sig 
      
     end
   end
  
  val lcm : z -> z -> z
  
  val eqb_spec : z -> z -> reflect
  
  val b2z : bool -> z
  
  val setbit : z -> z -> z
  
  val clearbit : z -> z -> z
  
  val lnot : z -> z
  
  val ones : z -> z
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : z -> z -> sumbool
    
    val min_case_strong :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : z -> z -> sumbool
   end
  
  val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : z -> z -> sumbool
  
  val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : z -> z -> sumbool
 end

val z_gt_dec : z -> z -> sumbool

val z_ge_dec : z -> z -> sumbool

val z_gt_le_dec : z -> z -> sumbool

val z_ge_lt_dec : z -> z -> sumbool

type 'x arrows_left = __

type 'x arrows_right = __

type tuple = __

val uncurry : __ list -> 'a1 arrows_left -> tuple -> 'a1

type 'x compare0 =
| LT
| EQ
| GT

module type Coq_OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare0
  
  val eq_dec : t -> t -> sumbool
 end

module Coq_OrderedTypeFacts : 
 functor (O:Coq_OrderedType) ->
 sig 
  module TO : 
   sig 
    type t = O.t
   end
  
  module IsTO : 
   sig 
    
   end
  
  module OrderTac : 
   sig 
    
   end
  
  val eq_dec : O.t -> O.t -> sumbool
  
  val lt_dec : O.t -> O.t -> sumbool
  
  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType : 
 functor (O:Coq_OrderedType) ->
 sig 
  module MO : 
   sig 
    module TO : 
     sig 
      type t = O.t
     end
    
    module IsTO : 
     sig 
      
     end
    
    module OrderTac : 
     sig 
      
     end
    
    val eq_dec : O.t -> O.t -> sumbool
    
    val lt_dec : O.t -> O.t -> sumbool
    
    val eqb : O.t -> O.t -> bool
   end
 end

module type Int = 
 sig 
  type t 
  
  val i2z : t -> z
  
  val _0 : t
  
  val _1 : t
  
  val _2 : t
  
  val _3 : t
  
  val plus : t -> t -> t
  
  val opp : t -> t
  
  val minus : t -> t -> t
  
  val mult : t -> t -> t
  
  val max : t -> t -> t
  
  val gt_le_dec : t -> t -> sumbool
  
  val ge_lt_dec : t -> t -> sumbool
  
  val eq_dec : t -> t -> sumbool
 end

module Z_as_Int : 
 sig 
  type t = z
  
  val _0 : z
  
  val _1 : z
  
  val _2 : z
  
  val _3 : z
  
  val plus : z -> z -> z
  
  val opp : z -> z
  
  val minus : z -> z -> z
  
  val mult : z -> z -> z
  
  val max : z -> z -> z
  
  val gt_le_dec : z -> z -> sumbool
  
  val ge_lt_dec : z -> z -> sumbool
  
  val eq_dec : z -> z -> sumbool
  
  val i2z : t -> z
 end

module MakeListOrdering : 
 functor (O:OrderedType) ->
 sig 
  module MO : 
   sig 
    module OrderTac : 
     sig 
      module OTF : 
       sig 
        type t = O.t
        
        val compare : t -> t -> comparison
        
        val eq_dec : t -> t -> sumbool
       end
      
      module TO : 
       sig 
        type t = OTF.t
        
        val compare : t -> t -> comparison
        
        val eq_dec : t -> t -> sumbool
       end
     end
    
    val eq_dec : O.t -> O.t -> sumbool
    
    val lt_dec : O.t -> O.t -> sumbool
    
    val eqb : O.t -> O.t -> bool
   end
 end

module MakeRaw : 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig 
  type elt = X.t
  
  type tree =
  | Leaf
  | Node of I.t * tree * X.t * tree
  
  val empty : tree
  
  val is_empty : tree -> bool
  
  val mem : X.t -> tree -> bool
  
  val min_elt : tree -> elt option
  
  val max_elt : tree -> elt option
  
  val choose : tree -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
  
  val elements_aux : X.t list -> tree -> X.t list
  
  val elements : tree -> X.t list
  
  val rev_elements_aux : X.t list -> tree -> X.t list
  
  val rev_elements : tree -> X.t list
  
  val cardinal : tree -> nat
  
  val maxdepth : tree -> nat
  
  val mindepth : tree -> nat
  
  val for_all : (elt -> bool) -> tree -> bool
  
  val exists_ : (elt -> bool) -> tree -> bool
  
  type enumeration =
  | End
  | More of elt * tree * enumeration
  
  val cons : tree -> enumeration -> enumeration
  
  val compare_more :
    X.t -> (enumeration -> comparison) -> enumeration -> comparison
  
  val compare_cont :
    tree -> (enumeration -> comparison) -> enumeration -> comparison
  
  val compare_end : enumeration -> comparison
  
  val compare : tree -> tree -> comparison
  
  val equal : tree -> tree -> bool
  
  val subsetl : (tree -> bool) -> X.t -> tree -> bool
  
  val subsetr : (tree -> bool) -> X.t -> tree -> bool
  
  val subset : tree -> tree -> bool
  
  type t = tree
  
  val height : t -> I.t
  
  val singleton : X.t -> tree
  
  val create : t -> X.t -> t -> tree
  
  val assert_false : t -> X.t -> t -> tree
  
  val bal : t -> X.t -> t -> tree
  
  val add : X.t -> tree -> tree
  
  val join : tree -> elt -> t -> t
  
  val remove_min : tree -> elt -> t -> (t, elt) prod
  
  val merge : tree -> tree -> tree
  
  val remove : X.t -> tree -> tree
  
  val concat : tree -> tree -> tree
  
  type triple = { t_left : t; t_in : bool; t_right : t }
  
  val t_left : triple -> t
  
  val t_in : triple -> bool
  
  val t_right : triple -> t
  
  val split : X.t -> tree -> triple
  
  val inter : tree -> tree -> tree
  
  val diff : tree -> tree -> tree
  
  val union : tree -> tree -> tree
  
  val filter : (elt -> bool) -> tree -> tree
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val ltb_tree : X.t -> tree -> bool
  
  val gtb_tree : X.t -> tree -> bool
  
  val isok : tree -> bool
  
  module MX : 
   sig 
    module OrderTac : 
     sig 
      module OTF : 
       sig 
        type t = X.t
        
        val compare : t -> t -> comparison
        
        val eq_dec : t -> t -> sumbool
       end
      
      module TO : 
       sig 
        type t = OTF.t
        
        val compare : t -> t -> comparison
        
        val eq_dec : t -> t -> sumbool
       end
     end
    
    val eq_dec : X.t -> X.t -> sumbool
    
    val lt_dec : X.t -> X.t -> sumbool
    
    val eqb : X.t -> X.t -> bool
   end
  
  type coq_R_min_elt =
  | R_min_elt_0 of tree
  | R_min_elt_1 of tree * I.t * tree * X.t * tree
  | R_min_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
     tree * elt option * coq_R_min_elt
  
  type coq_R_max_elt =
  | R_max_elt_0 of tree
  | R_max_elt_1 of tree * I.t * tree * X.t * tree
  | R_max_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
     tree * elt option * coq_R_max_elt
  
  module L : 
   sig 
    module MO : 
     sig 
      module OrderTac : 
       sig 
        module OTF : 
         sig 
          type t = X.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> sumbool
         end
        
        module TO : 
         sig 
          type t = OTF.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> sumbool
         end
       end
      
      val eq_dec : X.t -> X.t -> sumbool
      
      val lt_dec : X.t -> X.t -> sumbool
      
      val eqb : X.t -> X.t -> bool
     end
   end
  
  val flatten_e : enumeration -> elt list
  
  type coq_R_bal =
  | R_bal_0 of t * X.t * t
  | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t
     * tree
  | R_bal_4 of t * X.t * t
  | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t
     * tree
  | R_bal_8 of t * X.t * t
  
  type coq_R_remove_min =
  | R_remove_min_0 of tree * elt * t
  | R_remove_min_1 of tree * elt * t * I.t * tree * X.t * tree
     * (t, elt) prod * coq_R_remove_min * t * elt
  
  type coq_R_merge =
  | R_merge_0 of tree * tree
  | R_merge_1 of tree * tree * I.t * tree * X.t * tree
  | R_merge_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * elt
  
  type coq_R_concat =
  | R_concat_0 of tree * tree
  | R_concat_1 of tree * tree * I.t * tree * X.t * tree
  | R_concat_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * elt
  
  type coq_R_inter =
  | R_inter_0 of tree * tree
  | R_inter_1 of tree * tree * I.t * tree * X.t * tree
  | R_inter_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  | R_inter_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  
  type coq_R_diff =
  | R_diff_0 of tree * tree
  | R_diff_1 of tree * tree * I.t * tree * X.t * tree
  | R_diff_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  | R_diff_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  
  type coq_R_union =
  | R_union_0 of tree * tree
  | R_union_1 of tree * tree * I.t * tree * X.t * tree
  | R_union_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_union * tree * coq_R_union
 end

module IntMake : 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig 
  module Raw : 
   sig 
    type elt = X.t
    
    type tree =
    | Leaf
    | Node of I.t * tree * X.t * tree
    
    val empty : tree
    
    val is_empty : tree -> bool
    
    val mem : X.t -> tree -> bool
    
    val min_elt : tree -> elt option
    
    val max_elt : tree -> elt option
    
    val choose : tree -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
    
    val elements_aux : X.t list -> tree -> X.t list
    
    val elements : tree -> X.t list
    
    val rev_elements_aux : X.t list -> tree -> X.t list
    
    val rev_elements : tree -> X.t list
    
    val cardinal : tree -> nat
    
    val maxdepth : tree -> nat
    
    val mindepth : tree -> nat
    
    val for_all : (elt -> bool) -> tree -> bool
    
    val exists_ : (elt -> bool) -> tree -> bool
    
    type enumeration =
    | End
    | More of elt * tree * enumeration
    
    val cons : tree -> enumeration -> enumeration
    
    val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison
    
    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison
    
    val compare_end : enumeration -> comparison
    
    val compare : tree -> tree -> comparison
    
    val equal : tree -> tree -> bool
    
    val subsetl : (tree -> bool) -> X.t -> tree -> bool
    
    val subsetr : (tree -> bool) -> X.t -> tree -> bool
    
    val subset : tree -> tree -> bool
    
    type t = tree
    
    val height : t -> I.t
    
    val singleton : X.t -> tree
    
    val create : t -> X.t -> t -> tree
    
    val assert_false : t -> X.t -> t -> tree
    
    val bal : t -> X.t -> t -> tree
    
    val add : X.t -> tree -> tree
    
    val join : tree -> elt -> t -> t
    
    val remove_min : tree -> elt -> t -> (t, elt) prod
    
    val merge : tree -> tree -> tree
    
    val remove : X.t -> tree -> tree
    
    val concat : tree -> tree -> tree
    
    type triple = { t_left : t; t_in : bool; t_right : t }
    
    val t_left : triple -> t
    
    val t_in : triple -> bool
    
    val t_right : triple -> t
    
    val split : X.t -> tree -> triple
    
    val inter : tree -> tree -> tree
    
    val diff : tree -> tree -> tree
    
    val union : tree -> tree -> tree
    
    val filter : (elt -> bool) -> tree -> tree
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val ltb_tree : X.t -> tree -> bool
    
    val gtb_tree : X.t -> tree -> bool
    
    val isok : tree -> bool
    
    module MX : 
     sig 
      module OrderTac : 
       sig 
        module OTF : 
         sig 
          type t = X.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> sumbool
         end
        
        module TO : 
         sig 
          type t = OTF.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> sumbool
         end
       end
      
      val eq_dec : X.t -> X.t -> sumbool
      
      val lt_dec : X.t -> X.t -> sumbool
      
      val eqb : X.t -> X.t -> bool
     end
    
    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * I.t * tree * X.t * tree
    | R_min_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
       tree * elt option * coq_R_min_elt
    
    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * I.t * tree * X.t * tree
    | R_max_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
       tree * elt option * coq_R_max_elt
    
    module L : 
     sig 
      module MO : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = X.t
            
            val compare : t -> t -> comparison
            
            val eq_dec : t -> t -> sumbool
           end
          
          module TO : 
           sig 
            type t = OTF.t
            
            val compare : t -> t -> comparison
            
            val eq_dec : t -> t -> sumbool
           end
         end
        
        val eq_dec : X.t -> X.t -> sumbool
        
        val lt_dec : X.t -> X.t -> sumbool
        
        val eqb : X.t -> X.t -> bool
       end
     end
    
    val flatten_e : enumeration -> elt list
    
    type coq_R_bal =
    | R_bal_0 of t * X.t * t
    | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
    | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
    | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree
    | R_bal_4 of t * X.t * t
    | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
    | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
    | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree
    | R_bal_8 of t * X.t * t
    
    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * I.t * tree * X.t * tree
       * (t, elt) prod * coq_R_remove_min * t * elt
    
    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * I.t * tree * X.t * tree
    | R_merge_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree * t * elt
    
    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * I.t * tree * X.t * tree
    | R_concat_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree * t * elt
    
    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * I.t * tree * X.t * tree
    | R_inter_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
    
    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * I.t * tree * X.t * tree
    | R_diff_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
    
    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * I.t * tree * X.t * tree
    | R_union_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree * t * bool * t * tree * coq_R_union * tree * coq_R_union
   end
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> comparison
    
    val eq_dec : t -> t -> sumbool
   end
  
  type elt = X.t
  
  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  val this : t_ -> Raw.t
  
  type t = t_
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val remove : elt -> t -> t
  
  val singleton : elt -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val empty : t
  
  val is_empty : t -> bool
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val cardinal : t -> nat
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val eq_dec : t -> t -> sumbool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end

module type OrderedTypeOrig = 
 Coq_OrderedType

module Update_OT : 
 functor (O:OrderedTypeOrig) ->
 sig 
  type t = O.t
  
  val eq_dec : t -> t -> sumbool
  
  val compare : O.t -> O.t -> comparison
 end

module Coq_IntMake : 
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 sig 
  module X' : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> sumbool
    
    val compare : X.t -> X.t -> comparison
   end
  
  module MSet : 
   sig 
    module Raw : 
     sig 
      type elt = X.t
      
      type tree =
      | Leaf
      | Node of I.t * tree * X.t * tree
      
      val empty : tree
      
      val is_empty : tree -> bool
      
      val mem : X.t -> tree -> bool
      
      val min_elt : tree -> elt option
      
      val max_elt : tree -> elt option
      
      val choose : tree -> elt option
      
      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
      
      val elements_aux : X.t list -> tree -> X.t list
      
      val elements : tree -> X.t list
      
      val rev_elements_aux : X.t list -> tree -> X.t list
      
      val rev_elements : tree -> X.t list
      
      val cardinal : tree -> nat
      
      val maxdepth : tree -> nat
      
      val mindepth : tree -> nat
      
      val for_all : (elt -> bool) -> tree -> bool
      
      val exists_ : (elt -> bool) -> tree -> bool
      
      type enumeration =
      | End
      | More of elt * tree * enumeration
      
      val cons : tree -> enumeration -> enumeration
      
      val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison
      
      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison
      
      val compare_end : enumeration -> comparison
      
      val compare : tree -> tree -> comparison
      
      val equal : tree -> tree -> bool
      
      val subsetl : (tree -> bool) -> X.t -> tree -> bool
      
      val subsetr : (tree -> bool) -> X.t -> tree -> bool
      
      val subset : tree -> tree -> bool
      
      type t = tree
      
      val height : t -> I.t
      
      val singleton : X.t -> tree
      
      val create : t -> X.t -> t -> tree
      
      val assert_false : t -> X.t -> t -> tree
      
      val bal : t -> X.t -> t -> tree
      
      val add : X.t -> tree -> tree
      
      val join : tree -> elt -> t -> t
      
      val remove_min : tree -> elt -> t -> (t, elt) prod
      
      val merge : tree -> tree -> tree
      
      val remove : X.t -> tree -> tree
      
      val concat : tree -> tree -> tree
      
      type triple = { t_left : t; t_in : bool; t_right : t }
      
      val t_left : triple -> t
      
      val t_in : triple -> bool
      
      val t_right : triple -> t
      
      val split : X.t -> tree -> triple
      
      val inter : tree -> tree -> tree
      
      val diff : tree -> tree -> tree
      
      val union : tree -> tree -> tree
      
      val filter : (elt -> bool) -> tree -> tree
      
      val partition : (elt -> bool) -> t -> (t, t) prod
      
      val ltb_tree : X.t -> tree -> bool
      
      val gtb_tree : X.t -> tree -> bool
      
      val isok : tree -> bool
      
      module MX : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = X.t
            
            val compare : X.t -> X.t -> comparison
            
            val eq_dec : X.t -> X.t -> sumbool
           end
          
          module TO : 
           sig 
            type t = X.t
            
            val compare : X.t -> X.t -> comparison
            
            val eq_dec : X.t -> X.t -> sumbool
           end
         end
        
        val eq_dec : X.t -> X.t -> sumbool
        
        val lt_dec : X.t -> X.t -> sumbool
        
        val eqb : X.t -> X.t -> bool
       end
      
      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * I.t * tree * X.t * tree
      | R_min_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * elt option * coq_R_min_elt
      
      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * I.t * tree * X.t * tree
      | R_max_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * elt option * coq_R_max_elt
      
      module L : 
       sig 
        module MO : 
         sig 
          module OrderTac : 
           sig 
            module OTF : 
             sig 
              type t = X.t
              
              val compare : X.t -> X.t -> comparison
              
              val eq_dec : X.t -> X.t -> sumbool
             end
            
            module TO : 
             sig 
              type t = X.t
              
              val compare : X.t -> X.t -> comparison
              
              val eq_dec : X.t -> X.t -> sumbool
             end
           end
          
          val eq_dec : X.t -> X.t -> sumbool
          
          val lt_dec : X.t -> X.t -> sumbool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      val flatten_e : enumeration -> elt list
      
      type coq_R_bal =
      | R_bal_0 of t * X.t * t
      | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
      | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
      | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree
      | R_bal_4 of t * X.t * t
      | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
      | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
      | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree
      | R_bal_8 of t * X.t * t
      
      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * I.t * tree * X.t * tree
         * (t, elt) prod * coq_R_remove_min * t * elt
      
      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * I.t * tree * X.t * tree
      | R_merge_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * t * elt
      
      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * I.t * tree * X.t * tree
      | R_concat_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree
         * X.t * tree * t * elt
      
      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * I.t * tree * X.t * tree
      | R_inter_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
      
      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * I.t * tree * X.t * tree
      | R_diff_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
      
      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * I.t * tree * X.t * tree
      | R_union_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * t * bool * t * tree * coq_R_union * tree * coq_R_union
     end
    
    module E : 
     sig 
      type t = X.t
      
      val compare : X.t -> X.t -> comparison
      
      val eq_dec : X.t -> X.t -> sumbool
     end
    
    type elt = X.t
    
    type t_ =
      Raw.t
      (* singleton inductive, whose constructor was Mkt *)
    
    val this : t_ -> Raw.t
    
    type t = t_
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val remove : elt -> t -> t
    
    val singleton : elt -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val empty : t
    
    val is_empty : t -> bool
    
    val elements : t -> elt list
    
    val choose : t -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val cardinal : t -> nat
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val eq_dec : t -> t -> sumbool
    
    val compare : t -> t -> comparison
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
   end
  
  type elt = X.t
  
  type t = MSet.t
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> sumbool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  module MF : 
   sig 
    val eqb : X.t -> X.t -> bool
   end
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val compare : t -> t -> t compare0
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t compare0
    
    val eq_dec : t -> t -> sumbool
   end
 end

module Make : 
 functor (X:Coq_OrderedType) ->
 sig 
  module X' : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> sumbool
    
    val compare : X.t -> X.t -> comparison
   end
  
  module MSet : 
   sig 
    module Raw : 
     sig 
      type elt = X.t
      
      type tree =
      | Leaf
      | Node of Z_as_Int.t * tree * X.t * tree
      
      val empty : tree
      
      val is_empty : tree -> bool
      
      val mem : X.t -> tree -> bool
      
      val min_elt : tree -> elt option
      
      val max_elt : tree -> elt option
      
      val choose : tree -> elt option
      
      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
      
      val elements_aux : X.t list -> tree -> X.t list
      
      val elements : tree -> X.t list
      
      val rev_elements_aux : X.t list -> tree -> X.t list
      
      val rev_elements : tree -> X.t list
      
      val cardinal : tree -> nat
      
      val maxdepth : tree -> nat
      
      val mindepth : tree -> nat
      
      val for_all : (elt -> bool) -> tree -> bool
      
      val exists_ : (elt -> bool) -> tree -> bool
      
      type enumeration =
      | End
      | More of elt * tree * enumeration
      
      val cons : tree -> enumeration -> enumeration
      
      val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison
      
      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison
      
      val compare_end : enumeration -> comparison
      
      val compare : tree -> tree -> comparison
      
      val equal : tree -> tree -> bool
      
      val subsetl : (tree -> bool) -> X.t -> tree -> bool
      
      val subsetr : (tree -> bool) -> X.t -> tree -> bool
      
      val subset : tree -> tree -> bool
      
      type t = tree
      
      val height : t -> Z_as_Int.t
      
      val singleton : X.t -> tree
      
      val create : t -> X.t -> t -> tree
      
      val assert_false : t -> X.t -> t -> tree
      
      val bal : t -> X.t -> t -> tree
      
      val add : X.t -> tree -> tree
      
      val join : tree -> elt -> t -> t
      
      val remove_min : tree -> elt -> t -> (t, elt) prod
      
      val merge : tree -> tree -> tree
      
      val remove : X.t -> tree -> tree
      
      val concat : tree -> tree -> tree
      
      type triple = { t_left : t; t_in : bool; t_right : t }
      
      val t_left : triple -> t
      
      val t_in : triple -> bool
      
      val t_right : triple -> t
      
      val split : X.t -> tree -> triple
      
      val inter : tree -> tree -> tree
      
      val diff : tree -> tree -> tree
      
      val union : tree -> tree -> tree
      
      val filter : (elt -> bool) -> tree -> tree
      
      val partition : (elt -> bool) -> t -> (t, t) prod
      
      val ltb_tree : X.t -> tree -> bool
      
      val gtb_tree : X.t -> tree -> bool
      
      val isok : tree -> bool
      
      module MX : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = X.t
            
            val compare : X.t -> X.t -> comparison
            
            val eq_dec : X.t -> X.t -> sumbool
           end
          
          module TO : 
           sig 
            type t = X.t
            
            val compare : X.t -> X.t -> comparison
            
            val eq_dec : X.t -> X.t -> sumbool
           end
         end
        
        val eq_dec : X.t -> X.t -> sumbool
        
        val lt_dec : X.t -> X.t -> sumbool
        
        val eqb : X.t -> X.t -> bool
       end
      
      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * Z_as_Int.t * tree * X.t * tree
      | R_min_elt_2 of tree * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree * elt option * coq_R_min_elt
      
      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * Z_as_Int.t * tree * X.t * tree
      | R_max_elt_2 of tree * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree * elt option * coq_R_max_elt
      
      module L : 
       sig 
        module MO : 
         sig 
          module OrderTac : 
           sig 
            module OTF : 
             sig 
              type t = X.t
              
              val compare : X.t -> X.t -> comparison
              
              val eq_dec : X.t -> X.t -> sumbool
             end
            
            module TO : 
             sig 
              type t = X.t
              
              val compare : X.t -> X.t -> comparison
              
              val eq_dec : X.t -> X.t -> sumbool
             end
           end
          
          val eq_dec : X.t -> X.t -> sumbool
          
          val lt_dec : X.t -> X.t -> sumbool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      val flatten_e : enumeration -> elt list
      
      type coq_R_bal =
      | R_bal_0 of t * X.t * t
      | R_bal_1 of t * X.t * t * Z_as_Int.t * tree * X.t * tree
      | R_bal_2 of t * X.t * t * Z_as_Int.t * tree * X.t * tree
      | R_bal_3 of t * X.t * t * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree
      | R_bal_4 of t * X.t * t
      | R_bal_5 of t * X.t * t * Z_as_Int.t * tree * X.t * tree
      | R_bal_6 of t * X.t * t * Z_as_Int.t * tree * X.t * tree
      | R_bal_7 of t * X.t * t * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree
      | R_bal_8 of t * X.t * t
      
      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * X.t * 
         tree * (t, elt) prod * coq_R_remove_min * t * elt
      
      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_merge_2 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * elt
      
      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_concat_2 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * elt
      
      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_inter_2 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * bool * t * tree * coq_R_inter
         * tree * coq_R_inter
      | R_inter_3 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * bool * t * tree * coq_R_inter
         * tree * coq_R_inter
      
      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_diff_2 of tree * tree * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree * t * bool * t * tree * coq_R_diff * tree
         * coq_R_diff
      | R_diff_3 of tree * tree * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree * t * bool * t * tree * coq_R_diff * tree
         * coq_R_diff
      
      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_union_2 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * bool * t * tree * coq_R_union
         * tree * coq_R_union
     end
    
    module E : 
     sig 
      type t = X.t
      
      val compare : X.t -> X.t -> comparison
      
      val eq_dec : X.t -> X.t -> sumbool
     end
    
    type elt = X.t
    
    type t_ =
      Raw.t
      (* singleton inductive, whose constructor was Mkt *)
    
    val this : t_ -> Raw.t
    
    type t = t_
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val remove : elt -> t -> t
    
    val singleton : elt -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val empty : t
    
    val is_empty : t -> bool
    
    val elements : t -> elt list
    
    val choose : t -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val cardinal : t -> nat
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val eq_dec : t -> t -> sumbool
    
    val compare : t -> t -> comparison
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
   end
  
  type elt = X.t
  
  type t = MSet.t
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> sumbool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  module MF : 
   sig 
    val eqb : X.t -> X.t -> bool
   end
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val compare : t -> t -> t compare0
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t compare0
    
    val eq_dec : t -> t -> sumbool
   end
 end

module Raw : 
 functor (X:Coq_OrderedType) ->
 sig 
  module MX : 
   sig 
    module TO : 
     sig 
      type t = X.t
     end
    
    module IsTO : 
     sig 
      
     end
    
    module OrderTac : 
     sig 
      
     end
    
    val eq_dec : X.t -> X.t -> sumbool
    
    val lt_dec : X.t -> X.t -> sumbool
    
    val eqb : X.t -> X.t -> bool
   end
  
  module PX : 
   sig 
    module MO : 
     sig 
      module TO : 
       sig 
        type t = X.t
       end
      
      module IsTO : 
       sig 
        
       end
      
      module OrderTac : 
       sig 
        
       end
      
      val eq_dec : X.t -> X.t -> sumbool
      
      val lt_dec : X.t -> X.t -> sumbool
      
      val eqb : X.t -> X.t -> bool
     end
   end
  
  type key = X.t
  
  type 'elt t = (X.t, 'elt) prod list
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val mem : key -> 'a1 t -> bool
  
  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
     * 'elt coq_R_mem
  
  val coq_R_mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t
    -> bool -> 'a1 coq_R_mem -> 'a2
  
  val coq_R_mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t
    -> bool -> 'a1 coq_R_mem -> 'a2
  
  val mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
  
  val find : key -> 'a1 t -> 'a1 option
  
  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
     * 'elt coq_R_find
  
  val coq_R_find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
    'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2
  
  val coq_R_find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
    'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2
  
  val find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
     * 'elt coq_R_add
  
  val coq_R_add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) ->
    'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
  
  val coq_R_add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) ->
    'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
  
  val add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
  
  val remove : key -> 'a1 t -> 'a1 t
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
     * 'elt coq_R_remove
  
  val coq_R_remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
    t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
  
  val coq_R_remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
    t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
  
  val remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
  
  val elements : 'a1 t -> 'a1 t
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
  | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
     * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
  
  val coq_R_fold_rect :
    (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
    (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 ->
    'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
  
  val coq_R_fold_rec :
    (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
    (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 ->
    'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
  
  val fold_rect :
    (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
    (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3
    -> 'a2
  
  val fold_rec :
    (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
    (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3
    -> 'a2
  
  val coq_R_fold_correct :
    (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
    coq_R_fold
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
     X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
     X.t * 'elt * (X.t, 'elt) prod list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
  
  val coq_R_equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
    'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
    X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ ->
    'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
    'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
  
  val coq_R_equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
    'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
    X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ ->
    'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
    'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
  
  val equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
    'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t
    -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1
    t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
  
  val equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
    'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t
    -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1
    t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
  
  val coq_R_equal_correct :
    ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val option_cons :
    key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
  
  val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
  
  val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
  
  val fold_right_pair :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
  
  val map2_alt :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key, 'a3)
    prod list
  
  val at_least_one :
    'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
  
  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option
 end

module Coq_Raw : 
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 sig 
  type key = X.t
  
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t
  
  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2
  
  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2
  
  val height : 'a1 tree -> I.t
  
  val cardinal : 'a1 tree -> nat
  
  val empty : 'a1 tree
  
  val is_empty : 'a1 tree -> bool
  
  val mem : X.t -> 'a1 tree -> bool
  
  val find : X.t -> 'a1 tree -> 'a1 option
  
  val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  val remove_min :
    'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod
  
  val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
  
  val remove : X.t -> 'a1 tree -> 'a1 tree
  
  val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }
  
  val triple_rect :
    ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
  
  val triple_rec :
    ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
  
  val t_left : 'a1 triple -> 'a1 tree
  
  val t_opt : 'a1 triple -> 'a1 option
  
  val t_right : 'a1 triple -> 'a1 tree
  
  val split : X.t -> 'a1 tree -> 'a1 triple
  
  val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
  
  val elements_aux : (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
  
  val elements : 'a1 tree -> (key, 'a1) prod list
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
  
  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration
  
  val enumeration_rect :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2
  
  val enumeration_rec :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2
  
  val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
  
  val equal_more :
    ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool
  
  val equal_cont :
    ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool
  
  val equal_end : 'a1 enumeration -> bool
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
  
  val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
  
  val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
  
  val map2_opt :
    (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
    ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
    tree
  
  module Proofs : 
   sig 
    module MX : 
     sig 
      module TO : 
       sig 
        type t = X.t
       end
      
      module IsTO : 
       sig 
        
       end
      
      module OrderTac : 
       sig 
        
       end
      
      val eq_dec : X.t -> X.t -> sumbool
      
      val lt_dec : X.t -> X.t -> sumbool
      
      val eqb : X.t -> X.t -> bool
     end
    
    module PX : 
     sig 
      module MO : 
       sig 
        module TO : 
         sig 
          type t = X.t
         end
        
        module IsTO : 
         sig 
          
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> sumbool
        
        val lt_dec : X.t -> X.t -> sumbool
        
        val eqb : X.t -> X.t -> bool
       end
     end
    
    module L : 
     sig 
      module MX : 
       sig 
        module TO : 
         sig 
          type t = X.t
         end
        
        module IsTO : 
         sig 
          
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> sumbool
        
        val lt_dec : X.t -> X.t -> sumbool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module TO : 
           sig 
            type t = X.t
           end
          
          module IsTO : 
           sig 
            
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> sumbool
          
          val lt_dec : X.t -> X.t -> sumbool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      type key = X.t
      
      type 'elt t = (X.t, 'elt) prod list
      
      val empty : 'a1 t
      
      val is_empty : 'a1 t -> bool
      
      val mem : key -> 'a1 t -> bool
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt t
      | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
         * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
      
      val mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
      
      val find : key -> 'a1 t -> 'a1 option
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt t
      | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
         * 'elt coq_R_find
      
      val coq_R_find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
        'a2
      
      val coq_R_find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
        'a2
      
      val find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
      
      val add : key -> 'a1 -> 'a1 t -> 'a1 t
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt t
      | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
         * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
      
      val add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
        -> 'a2
      
      val add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
        -> 'a2
      
      val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
      
      val remove : key -> 'a1 t -> 'a1 t
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt t
      | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
         * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
      
      val remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
      
      val elements : 'a1 t -> 'a1 t
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
      
      type ('elt, 'a) coq_R_fold =
      | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
      | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
         * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
      
      val coq_R_fold_rect :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) ->
        (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
        coq_R_fold -> 'a2
      
      val coq_R_fold_rec :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) ->
        (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
        coq_R_fold -> 'a2
      
      val fold_rect :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
        'a1 t -> 'a3 -> 'a2
      
      val fold_rec :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
        'a1 t -> 'a3 -> 'a2
      
      val coq_R_fold_correct :
        (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
      
      type 'elt coq_R_equal =
      | R_equal_0 of 'elt t * 'elt t
      | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
         * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
      | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
         * X.t * 'elt * (X.t, 'elt) prod list * X.t compare0
      | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
      
      val coq_R_equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
        'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list
        -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 ->
        __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
        __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
      
      val coq_R_equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
        'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list
        -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 ->
        __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
        __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
      
      val equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t ->
        'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
        ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t
        -> 'a1 t -> 'a2
      
      val equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t ->
        'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
        ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t
        -> 'a1 t -> 'a2
      
      val coq_R_equal_correct :
        ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
      
      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val option_cons :
        key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
      
      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
      
      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
      
      val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
      
      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
      
      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
        'a3) prod list
      
      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
      
      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end
    
    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    
    val coq_R_mem_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2
    
    val coq_R_mem_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2
    
    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    
    val coq_R_find_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
    
    val coq_R_find_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
    
    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
    
    val coq_R_bal_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2
    
    val coq_R_bal_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2
    
    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    
    val coq_R_add_rect :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
      'a2
    
    val coq_R_add_rec :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
      'a2
    
    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree, (key, 'elt) prod) prod
       * 'elt coq_R_remove_min * 'elt tree * (key, 'elt) prod
    
    val coq_R_remove_min_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
      'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min ->
      'a2
    
    val coq_R_remove_min_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
      'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min ->
      'a2
    
    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key, 'elt) prod * key * 'elt
    
    val coq_R_merge_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key, 'a1)
      prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
      tree -> 'a1 coq_R_merge -> 'a2
    
    val coq_R_merge_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key, 'a1)
      prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
      tree -> 'a1 coq_R_merge -> 'a2
    
    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    
    val coq_R_remove_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
    
    val coq_R_remove_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
    
    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key, 'elt) prod
    
    val coq_R_concat_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key, 'a1)
      prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      coq_R_concat -> 'a2
    
    val coq_R_concat_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key, 'a1)
      prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      coq_R_concat -> 'a2
    
    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    
    val coq_R_split_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2
    
    val coq_R_split_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2
    
    type ('elt, 'elt') coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
       * ('elt, 'elt') coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
       * ('elt, 'elt') coq_R_map_option
    
    val coq_R_map_option_rect :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3
    
    val coq_R_map_option_rec :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3
    
    type ('elt, 'elt', 'elt'') coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'elt' tree
    | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt' tree * key * 'elt' * 'elt' tree * I.t
       * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt' tree * key * 'elt' * 'elt' tree * I.t
       * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    
    val coq_R_map2_opt_rect :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
    
    val coq_R_map2_opt_rec :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
    
    val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
    
    val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
   end
 end

module Coq0_IntMake : 
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 sig 
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t compare0
    
    val eq_dec : t -> t -> sumbool
   end
  
  module Raw : 
   sig 
    type key = X.t
    
    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.t
    
    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2
    
    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2
    
    val height : 'a1 tree -> I.t
    
    val cardinal : 'a1 tree -> nat
    
    val empty : 'a1 tree
    
    val is_empty : 'a1 tree -> bool
    
    val mem : X.t -> 'a1 tree -> bool
    
    val find : X.t -> 'a1 tree -> 'a1 option
    
    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod
    
    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val remove : X.t -> 'a1 tree -> 'a1 tree
    
    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }
    
    val triple_rect :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val triple_rec :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val t_left : 'a1 triple -> 'a1 tree
    
    val t_opt : 'a1 triple -> 'a1 option
    
    val t_right : 'a1 triple -> 'a1 tree
    
    val split : X.t -> 'a1 tree -> 'a1 triple
    
    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
    
    val elements : 'a1 tree -> (key, 'a1) prod list
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
    
    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration
    
    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
    
    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_end : 'a1 enumeration -> bool
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
    
    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
    
    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree
    
    module Proofs : 
     sig 
      module MX : 
       sig 
        module TO : 
         sig 
          type t = X.t
         end
        
        module IsTO : 
         sig 
          
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> sumbool
        
        val lt_dec : X.t -> X.t -> sumbool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module TO : 
           sig 
            type t = X.t
           end
          
          module IsTO : 
           sig 
            
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> sumbool
          
          val lt_dec : X.t -> X.t -> sumbool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      module L : 
       sig 
        module MX : 
         sig 
          module TO : 
           sig 
            type t = X.t
           end
          
          module IsTO : 
           sig 
            
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> sumbool
          
          val lt_dec : X.t -> X.t -> sumbool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module TO : 
             sig 
              type t = X.t
             end
            
            module IsTO : 
             sig 
              
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> sumbool
            
            val lt_dec : X.t -> X.t -> sumbool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        type key = X.t
        
        type 'elt t = (X.t, 'elt) prod list
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val mem : key -> 'a1 t -> bool
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
           * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
        
        val find : key -> 'a1 t -> 'a1 option
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
           * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
        
        val remove : key -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
           'elt t * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
        
        val elements : 'a1 t -> 'a1 t
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
        | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
           'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
        
        val coq_R_fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val coq_R_fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
        
        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * X.t compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
        
        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
          -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
          coq_R_equal -> 'a2
        
        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
          -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
          coq_R_equal -> 'a2
        
        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a2
        
        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a2
        
        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
        
        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
        
        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
        
        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
        
        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list
        
        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
        
        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find
      
      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
      
      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
      
      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
      
      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
      
      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2
      
      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * I.t * ('elt tree, (key, 'elt) prod) prod
         * 'elt coq_R_remove_min * 'elt tree * (key, 'elt) prod
      
      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
        'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2
      
      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
        'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2
      
      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key, 'elt) prod * key * 'elt
      
      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
      
      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
      
      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key, 'elt) prod
      
      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2
      
      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2
      
      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      
      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2
      
      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2
      
      type ('elt, 'elt') coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
         * ('elt, 'elt') coq_R_map_option
      
      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3
      
      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3
      
      type ('elt, 'elt', 'elt'') coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'elt' tree
      | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt' tree * key * 'elt' * 'elt' tree * 
         I.t * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt' tree * key * 'elt' * 'elt' tree * 
         I.t * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      
      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
      
      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
      
      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end
  
  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)
  
  val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
  
  val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
  
  val this : 'a1 bst -> 'a1 Raw.tree
  
  type 'elt t = 'elt bst
  
  type key = E.t
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : key -> 'a1 t -> 'a1 t
  
  val mem : key -> 'a1 t -> bool
  
  val find : key -> 'a1 t -> 'a1 option
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val elements : 'a1 t -> (key, 'a1) prod list
  
  val cardinal : 'a1 t -> nat
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Coq_Make : 
 functor (X:Coq_OrderedType) ->
 sig 
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t compare0
    
    val eq_dec : t -> t -> sumbool
   end
  
  module Raw : 
   sig 
    type key = X.t
    
    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
    
    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2
    
    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2
    
    val height : 'a1 tree -> Z_as_Int.t
    
    val cardinal : 'a1 tree -> nat
    
    val empty : 'a1 tree
    
    val is_empty : 'a1 tree -> bool
    
    val mem : X.t -> 'a1 tree -> bool
    
    val find : X.t -> 'a1 tree -> 'a1 option
    
    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod
    
    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val remove : X.t -> 'a1 tree -> 'a1 tree
    
    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }
    
    val triple_rect :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val triple_rec :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val t_left : 'a1 triple -> 'a1 tree
    
    val t_opt : 'a1 triple -> 'a1 option
    
    val t_right : 'a1 triple -> 'a1 tree
    
    val split : X.t -> 'a1 tree -> 'a1 triple
    
    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
    
    val elements : 'a1 tree -> (key, 'a1) prod list
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
    
    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration
    
    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
    
    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_end : 'a1 enumeration -> bool
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
    
    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
    
    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree
    
    module Proofs : 
     sig 
      module MX : 
       sig 
        module TO : 
         sig 
          type t = X.t
         end
        
        module IsTO : 
         sig 
          
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> sumbool
        
        val lt_dec : X.t -> X.t -> sumbool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module TO : 
           sig 
            type t = X.t
           end
          
          module IsTO : 
           sig 
            
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> sumbool
          
          val lt_dec : X.t -> X.t -> sumbool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      module L : 
       sig 
        module MX : 
         sig 
          module TO : 
           sig 
            type t = X.t
           end
          
          module IsTO : 
           sig 
            
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> sumbool
          
          val lt_dec : X.t -> X.t -> sumbool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module TO : 
             sig 
              type t = X.t
             end
            
            module IsTO : 
             sig 
              
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> sumbool
            
            val lt_dec : X.t -> X.t -> sumbool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        type key = X.t
        
        type 'elt t = (X.t, 'elt) prod list
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val mem : key -> 'a1 t -> bool
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
           * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
        
        val find : key -> 'a1 t -> 'a1 option
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
           * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
        
        val remove : key -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
           'elt t * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
        
        val elements : 'a1 t -> 'a1 t
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
        | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
           'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
        
        val coq_R_fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val coq_R_fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
        
        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * X.t compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
        
        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
          -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
          coq_R_equal -> 'a2
        
        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
          -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
          coq_R_equal -> 'a2
        
        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a2
        
        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a2
        
        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
        
        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
        
        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
        
        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
        
        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list
        
        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
        
        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      
      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2
      
      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2
      
      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
      
      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
      
      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2
      
      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.t
         * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
         * 'elt tree * (key, 'elt) prod
      
      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod -> 'a1 coq_R_remove_min -> 'a2
      
      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod -> 'a1 coq_R_remove_min -> 'a2
      
      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key, 'elt) prod * key * 'elt
      
      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key -> 'a1 -> __ ->
        'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
      
      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key -> 'a1 -> __ ->
        'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2
      
      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key, 'elt) prod
      
      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
      
      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
      
      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      
      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
      
      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
      
      type ('elt, 'elt') coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      
      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3
      
      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3
      
      type ('elt, 'elt', 'elt'') coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'elt' tree
      | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt' * 'elt' tree
         * Z_as_Int.t * 'elt' tree * 'elt' option * 'elt' tree * 'elt''
         * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt' * 'elt' tree
         * Z_as_Int.t * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      
      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
      
      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
      
      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end
  
  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)
  
  val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
  
  val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
  
  val this : 'a1 bst -> 'a1 Raw.tree
  
  type 'elt t = 'elt bst
  
  type key = E.t
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : key -> 'a1 t -> 'a1 t
  
  val mem : key -> 'a1 t -> bool
  
  val find : key -> 'a1 t -> 'a1 option
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val elements : 'a1 t -> (key, 'a1) prod list
  
  val cardinal : 'a1 t -> nat
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

type 'a comparable =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_Comparable *)

val compare1 : 'a1 comparable -> 'a1 -> 'a1 -> comparison

val natComparable : nat comparable

val pairComparable :
  'a1 comparable -> 'a2 comparable -> ('a1, 'a2) prod comparable

val compare_eqb : 'a1 comparable -> 'a1 -> 'a1 -> bool

val compare_eqdec : 'a1 comparable -> 'a1 -> 'a1 -> sumbool

type 'a finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

val all_list : 'a1 finite -> 'a1 list

type 'a alphabet = { alphabetComparable : 'a comparable;
                     alphabetFinite : 'a finite }

val alphabetComparable : 'a1 alphabet -> 'a1 comparable

val alphabetFinite : 'a1 alphabet -> 'a1 finite

module type ComparableM = 
 sig 
  type t 
  
  val tComparable : t comparable
 end

module OrderedTypeAlt_from_ComparableM : 
 functor (C:ComparableM) ->
 sig 
  type t = C.t
  
  val compare : t -> t -> comparison
 end

module OrderedType_from_ComparableM : 
 functor (C:ComparableM) ->
 sig 
  module Alt : 
   sig 
    type t = C.t
    
    val compare : t -> t -> comparison
   end
  
  type t = Alt.t
  
  val compare : Alt.t -> Alt.t -> Alt.t compare0
  
  val eq_dec : Alt.t -> Alt.t -> sumbool
 end

module type T = 
 sig 
  type terminal 
  
  type nonterminal 
  
  val coq_TerminalAlph : terminal alphabet
  
  val coq_NonTerminalAlph : nonterminal alphabet
  
  type symbol =
  | T of terminal
  | NT of nonterminal
  
  val symbol_rect :
    (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
  
  val symbol_rec : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
  
  val coq_SymbolAlph : symbol alphabet
  
  type symbol_semantic_type 
  
  type production 
  
  val coq_ProductionAlph : production alphabet
  
  val prod_lhs : production -> nonterminal
  
  val prod_rhs_rev : production -> symbol list
  
  val prod_action : production -> symbol_semantic_type arrows_left
 end

module type Coq_T = 
 sig 
  module Gram : 
   T
  
  type noninitstate 
  
  val coq_NonInitStateAlph : noninitstate alphabet
  
  type initstate 
  
  val coq_InitStateAlph : initstate alphabet
  
  val last_symb_of_non_init_state : noninitstate -> Gram.symbol
  
  type state =
  | Init of initstate
  | Ninit of noninitstate
  
  val state_rect :
    (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1
  
  val state_rec : (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1
  
  val coq_StateAlph : state alphabet
  
  type lookahead_action =
  | Shift_act of noninitstate
  | Reduce_act of Gram.production
  | Fail_act
  
  val lookahead_action_rect :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> lookahead_action -> 'a1
  
  val lookahead_action_rec :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> lookahead_action -> 'a1
  
  type action =
  | Default_reduce_act of Gram.production
  | Lookahead_act of (Gram.terminal -> lookahead_action)
  
  val action_rect :
    (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) -> 'a1)
    -> action -> 'a1
  
  val action_rec :
    (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) -> 'a1)
    -> action -> 'a1
  
  type item = { prod_item : Gram.production; dot_pos_item : nat;
                lookaheads_item : Gram.terminal list }
  
  val item_rect :
    (Gram.production -> nat -> Gram.terminal list -> 'a1) -> item -> 'a1
  
  val item_rec :
    (Gram.production -> nat -> Gram.terminal list -> 'a1) -> item -> 'a1
  
  val prod_item : item -> Gram.production
  
  val dot_pos_item : item -> nat
  
  val lookaheads_item : item -> Gram.terminal list
  
  module GramDefs : 
   sig 
    type token = (Gram.terminal, Gram.symbol_semantic_type) sigT
    
    type parse_tree =
    | Terminal_pt of Gram.terminal * Gram.symbol_semantic_type
    | Non_terminal_pt of Gram.production * token list * tuple
       * parse_tree_list
    and parse_tree_list =
    | Nil_ptl
    | Cons_ptl of Gram.symbol * token list * Gram.symbol_semantic_type
       * parse_tree * Gram.symbol list * token list * tuple * parse_tree_list
    
    val parse_tree_rect :
      (Gram.terminal -> Gram.symbol_semantic_type -> 'a1) -> (Gram.production
      -> token list -> tuple -> parse_tree_list -> 'a1) -> Gram.symbol ->
      token list -> Gram.symbol_semantic_type -> parse_tree -> 'a1
    
    val parse_tree_rec :
      (Gram.terminal -> Gram.symbol_semantic_type -> 'a1) -> (Gram.production
      -> token list -> tuple -> parse_tree_list -> 'a1) -> Gram.symbol ->
      token list -> Gram.symbol_semantic_type -> parse_tree -> 'a1
    
    val parse_tree_list_rect :
      'a1 -> (Gram.symbol -> token list -> Gram.symbol_semantic_type ->
      parse_tree -> Gram.symbol list -> token list -> tuple ->
      parse_tree_list -> 'a1 -> 'a1) -> Gram.symbol list -> token list ->
      tuple -> parse_tree_list -> 'a1
    
    val parse_tree_list_rec :
      'a1 -> (Gram.symbol -> token list -> Gram.symbol_semantic_type ->
      parse_tree -> Gram.symbol list -> token list -> tuple ->
      parse_tree_list -> 'a1 -> 'a1) -> Gram.symbol list -> token list ->
      tuple -> parse_tree_list -> 'a1
    
    val pt_size :
      Gram.symbol -> token list -> Gram.symbol_semantic_type -> parse_tree ->
      nat
    
    val ptl_size :
      Gram.symbol list -> token list -> tuple -> parse_tree_list -> nat
   end
  
  val start_nt : initstate -> Gram.nonterminal
  
  val action_table : state -> action
  
  val goto_table : state -> Gram.nonterminal -> noninitstate option
  
  val past_symb_of_non_init_state : noninitstate -> Gram.symbol list
  
  val past_state_of_non_init_state : noninitstate -> (state -> bool) list
  
  val items_of_state : state -> item list
  
  val nullable_nterm : Gram.nonterminal -> bool
  
  val first_nterm : Gram.nonterminal -> Gram.terminal list
 end

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Cons0 of 'a * 'a stream

val hd : 'a1 stream -> 'a1

val tl : 'a1 stream -> 'a1 stream

module Coq0_Make : 
 functor (A:Coq_T) ->
 sig 
  val singleton_state_pred : A.state -> A.state -> bool
  
  val past_state_of_state : A.state -> (A.state -> bool) list
  
  val head_symbs_of_state : A.state -> A.Gram.symbol list
  
  val head_states_of_state : A.state -> (A.state -> bool) list
  
  val is_prefix : A.Gram.symbol list -> A.Gram.symbol list -> bool
  
  val is_shift_head_symbs : unit0 -> bool
  
  val is_goto_head_symbs : unit0 -> bool
  
  val is_prefix_pred :
    (A.state -> bool) list -> (A.state -> bool) list -> bool
  
  val is_shift_past_state : unit0 -> bool
  
  val is_goto_past_state : unit0 -> bool
  
  val is_state_valid_after_pop :
    A.state -> A.Gram.symbol list -> (A.state -> bool) list -> bool
  
  val is_valid_for_reduce : A.state -> A.Gram.production -> bool
  
  val is_reduce_ok : unit0 -> bool
  
  val is_safe : unit0 -> bool
 end

module Coq1_Make : 
 functor (A:Coq_T) ->
 sig 
  type 'a result =
  | Err
  | OK of 'a
  
  val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
  
  val bind2 :
    ('a1, 'a2) prod result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
  
  val app_str : 'a1 list -> 'a1 stream -> 'a1 stream
  
  type noninitstate_type = A.Gram.symbol_semantic_type
  
  type stack = (A.noninitstate, noninitstate_type) sigT list
  
  val state_of_stack : A.initstate -> stack -> A.state
  
  val pop :
    A.Gram.symbol list -> stack -> 'a1 arrows_right -> (stack, 'a1) prod
    result
  
  type step_result =
  | Fail_sr
  | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token stream
  | Progress_sr of stack * A.GramDefs.token stream
  
  val step_result_rect :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    stream -> 'a1) -> (stack -> A.GramDefs.token stream -> 'a1) ->
    step_result -> 'a1
  
  val step_result_rec :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    stream -> 'a1) -> (stack -> A.GramDefs.token stream -> 'a1) ->
    step_result -> 'a1
  
  val prod_action' :
    A.Gram.production -> A.Gram.symbol_semantic_type arrows_right
  
  val reduce_step :
    A.initstate -> stack -> A.Gram.production -> A.GramDefs.token stream ->
    step_result result
  
  val step :
    A.initstate -> stack -> A.GramDefs.token stream -> step_result result
  
  type parse_result =
  | Fail_pr
  | Timeout_pr
  | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token stream
  
  val parse_result_rect :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
  
  val parse_result_rec :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
  
  val parse_fix :
    A.initstate -> stack -> A.GramDefs.token stream -> nat -> parse_result
    result
  
  val parse :
    A.initstate -> A.GramDefs.token stream -> nat -> parse_result result
 end

module Coq2_Make : 
 functor (A:Coq_T) ->
 functor (Inter:sig 
  type 'a result =
  | Err
  | OK of 'a
  
  val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
  
  val bind2 :
    ('a1, 'a2) prod result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
  
  val app_str : 'a1 list -> 'a1 stream -> 'a1 stream
  
  type noninitstate_type = A.Gram.symbol_semantic_type
  
  type stack = (A.noninitstate, noninitstate_type) sigT list
  
  val state_of_stack : A.initstate -> stack -> A.state
  
  val pop :
    A.Gram.symbol list -> stack -> 'a1 arrows_right -> (stack, 'a1) prod
    result
  
  type step_result =
  | Fail_sr
  | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token stream
  | Progress_sr of stack * A.GramDefs.token stream
  
  val step_result_rect :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    stream -> 'a1) -> (stack -> A.GramDefs.token stream -> 'a1) ->
    step_result -> 'a1
  
  val step_result_rec :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    stream -> 'a1) -> (stack -> A.GramDefs.token stream -> 'a1) ->
    step_result -> 'a1
  
  val prod_action' :
    A.Gram.production -> A.Gram.symbol_semantic_type arrows_right
  
  val reduce_step :
    A.initstate -> stack -> A.Gram.production -> A.GramDefs.token stream ->
    step_result result
  
  val step :
    A.initstate -> stack -> A.GramDefs.token stream -> step_result result
  
  type parse_result =
  | Fail_pr
  | Timeout_pr
  | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token stream
  
  val parse_result_rect :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
  
  val parse_result_rec :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
  
  val parse_fix :
    A.initstate -> stack -> A.GramDefs.token stream -> nat -> parse_result
    result
  
  val parse :
    A.initstate -> A.GramDefs.token stream -> nat -> parse_result result
 end) ->
 sig 
  module Valid : 
   sig 
    val singleton_state_pred : A.state -> A.state -> bool
    
    val past_state_of_state : A.state -> (A.state -> bool) list
    
    val head_symbs_of_state : A.state -> A.Gram.symbol list
    
    val head_states_of_state : A.state -> (A.state -> bool) list
    
    val is_prefix : A.Gram.symbol list -> A.Gram.symbol list -> bool
    
    val is_shift_head_symbs : unit0 -> bool
    
    val is_goto_head_symbs : unit0 -> bool
    
    val is_prefix_pred :
      (A.state -> bool) list -> (A.state -> bool) list -> bool
    
    val is_shift_past_state : unit0 -> bool
    
    val is_goto_past_state : unit0 -> bool
    
    val is_state_valid_after_pop :
      A.state -> A.Gram.symbol list -> (A.state -> bool) list -> bool
    
    val is_valid_for_reduce : A.state -> A.Gram.production -> bool
    
    val is_reduce_ok : unit0 -> bool
    
    val is_safe : unit0 -> bool
   end
  
  val state_stack_of_stack :
    A.initstate -> Inter.stack -> (A.state -> bool) list
  
  val symb_stack_of_stack : Inter.stack -> A.Gram.symbol list
  
  val internal_eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
  
  val parse_with_safe :
    A.initstate -> A.GramDefs.token stream -> nat -> Inter.parse_result
 end

module Coq3_Make : 
 functor (A:Coq_T) ->
 functor (Inter:sig 
  type 'a result =
  | Err
  | OK of 'a
  
  val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
  
  val bind2 :
    ('a1, 'a2) prod result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
  
  val app_str : 'a1 list -> 'a1 stream -> 'a1 stream
  
  type noninitstate_type = A.Gram.symbol_semantic_type
  
  type stack = (A.noninitstate, noninitstate_type) sigT list
  
  val state_of_stack : A.initstate -> stack -> A.state
  
  val pop :
    A.Gram.symbol list -> stack -> 'a1 arrows_right -> (stack, 'a1) prod
    result
  
  type step_result =
  | Fail_sr
  | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token stream
  | Progress_sr of stack * A.GramDefs.token stream
  
  val step_result_rect :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    stream -> 'a1) -> (stack -> A.GramDefs.token stream -> 'a1) ->
    step_result -> 'a1
  
  val step_result_rec :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    stream -> 'a1) -> (stack -> A.GramDefs.token stream -> 'a1) ->
    step_result -> 'a1
  
  val prod_action' :
    A.Gram.production -> A.Gram.symbol_semantic_type arrows_right
  
  val reduce_step :
    A.initstate -> stack -> A.Gram.production -> A.GramDefs.token stream ->
    step_result result
  
  val step :
    A.initstate -> stack -> A.GramDefs.token stream -> step_result result
  
  type parse_result =
  | Fail_pr
  | Timeout_pr
  | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token stream
  
  val parse_result_rect :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
  
  val parse_result_rec :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
  
  val parse_fix :
    A.initstate -> stack -> A.GramDefs.token stream -> nat -> parse_result
    result
  
  val parse :
    A.initstate -> A.GramDefs.token stream -> nat -> parse_result result
 end) ->
 sig 
  val internal_eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
 end

module Coq4_Make : 
 functor (A:Coq_T) ->
 sig 
  module TerminalComparableM : 
   sig 
    type t = A.Gram.terminal
    
    val tComparable : t comparable
   end
  
  module TerminalOrderedType : 
   sig 
    module Alt : 
     sig 
      type t = TerminalComparableM.t
      
      val compare : t -> t -> comparison
     end
    
    type t = Alt.t
    
    val compare : Alt.t -> Alt.t -> Alt.t compare0
    
    val eq_dec : Alt.t -> Alt.t -> sumbool
   end
  
  module StateProdPosComparableM : 
   sig 
    type t = ((A.state, A.Gram.production) prod, nat) prod
    
    val tComparable : t comparable
   end
  
  module StateProdPosOrderedType : 
   sig 
    module Alt : 
     sig 
      type t = StateProdPosComparableM.t
      
      val compare : t -> t -> comparison
     end
    
    type t = Alt.t
    
    val compare : Alt.t -> Alt.t -> Alt.t compare0
    
    val eq_dec : Alt.t -> Alt.t -> sumbool
   end
  
  module TerminalSet : 
   sig 
    module X' : 
     sig 
      type t = TerminalOrderedType.Alt.t
      
      val eq_dec :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
      
      val compare :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> comparison
     end
    
    module MSet : 
     sig 
      module Raw : 
       sig 
        type elt = TerminalOrderedType.Alt.t
        
        type tree =
        | Leaf
        | Node of Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree
        
        val empty : tree
        
        val is_empty : tree -> bool
        
        val mem : TerminalOrderedType.Alt.t -> tree -> bool
        
        val min_elt : tree -> elt option
        
        val max_elt : tree -> elt option
        
        val choose : tree -> elt option
        
        val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
        
        val elements_aux :
          TerminalOrderedType.Alt.t list -> tree -> TerminalOrderedType.Alt.t
          list
        
        val elements : tree -> TerminalOrderedType.Alt.t list
        
        val rev_elements_aux :
          TerminalOrderedType.Alt.t list -> tree -> TerminalOrderedType.Alt.t
          list
        
        val rev_elements : tree -> TerminalOrderedType.Alt.t list
        
        val cardinal : tree -> nat
        
        val maxdepth : tree -> nat
        
        val mindepth : tree -> nat
        
        val for_all : (elt -> bool) -> tree -> bool
        
        val exists_ : (elt -> bool) -> tree -> bool
        
        type enumeration =
        | End
        | More of elt * tree * enumeration
        
        val cons : tree -> enumeration -> enumeration
        
        val compare_more :
          TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
          enumeration -> comparison
        
        val compare_cont :
          tree -> (enumeration -> comparison) -> enumeration -> comparison
        
        val compare_end : enumeration -> comparison
        
        val compare : tree -> tree -> comparison
        
        val equal : tree -> tree -> bool
        
        val subsetl :
          (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
        
        val subsetr :
          (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
        
        val subset : tree -> tree -> bool
        
        type t = tree
        
        val height : t -> Z_as_Int.t
        
        val singleton : TerminalOrderedType.Alt.t -> tree
        
        val create : t -> TerminalOrderedType.Alt.t -> t -> tree
        
        val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree
        
        val bal : t -> TerminalOrderedType.Alt.t -> t -> tree
        
        val add : TerminalOrderedType.Alt.t -> tree -> tree
        
        val join : tree -> elt -> t -> t
        
        val remove_min : tree -> elt -> t -> (t, elt) prod
        
        val merge : tree -> tree -> tree
        
        val remove : TerminalOrderedType.Alt.t -> tree -> tree
        
        val concat : tree -> tree -> tree
        
        type triple = { t_left : t; t_in : bool; t_right : t }
        
        val t_left : triple -> t
        
        val t_in : triple -> bool
        
        val t_right : triple -> t
        
        val split : TerminalOrderedType.Alt.t -> tree -> triple
        
        val inter : tree -> tree -> tree
        
        val diff : tree -> tree -> tree
        
        val union : tree -> tree -> tree
        
        val filter : (elt -> bool) -> tree -> tree
        
        val partition : (elt -> bool) -> t -> (t, t) prod
        
        val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool
        
        val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool
        
        val isok : tree -> bool
        
        module MX : 
         sig 
          module OrderTac : 
           sig 
            module OTF : 
             sig 
              type t = TerminalOrderedType.Alt.t
              
              val compare :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                comparison
              
              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                sumbool
             end
            
            module TO : 
             sig 
              type t = TerminalOrderedType.Alt.t
              
              val compare :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                comparison
              
              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                sumbool
             end
           end
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
          
          val lt_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
          
          val eqb :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
        
        type coq_R_min_elt =
        | R_min_elt_0 of tree
        | R_min_elt_1 of tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t
           * tree
        | R_min_elt_2 of tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t
           * tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree
           * elt option * coq_R_min_elt
        
        type coq_R_max_elt =
        | R_max_elt_0 of tree
        | R_max_elt_1 of tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t
           * tree
        | R_max_elt_2 of tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t
           * tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree
           * elt option * coq_R_max_elt
        
        module L : 
         sig 
          module MO : 
           sig 
            module OrderTac : 
             sig 
              module OTF : 
               sig 
                type t = TerminalOrderedType.Alt.t
                
                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  sumbool
               end
              
              module TO : 
               sig 
                type t = TerminalOrderedType.Alt.t
                
                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  sumbool
               end
             end
            
            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              sumbool
            
            val lt_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              sumbool
            
            val eqb :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end
         end
        
        val flatten_e : enumeration -> elt list
        
        type coq_R_bal =
        | R_bal_0 of t * TerminalOrderedType.Alt.t * t
        | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree
        | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree
        | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_bal_4 of t * TerminalOrderedType.Alt.t * t
        | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree
        | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree
        | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_bal_8 of t * TerminalOrderedType.Alt.t * t
        
        type coq_R_remove_min =
        | R_remove_min_0 of tree * elt * t
        | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * (t, elt) prod
           * coq_R_remove_min * t * elt
        
        type coq_R_merge =
        | R_merge_0 of tree * tree
        | R_merge_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_merge_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * elt
        
        type coq_R_concat =
        | R_concat_0 of tree * tree
        | R_concat_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_concat_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * elt
        
        type coq_R_inter =
        | R_inter_0 of tree * tree
        | R_inter_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_inter_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_inter * tree * coq_R_inter
        | R_inter_3 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_inter * tree * coq_R_inter
        
        type coq_R_diff =
        | R_diff_0 of tree * tree
        | R_diff_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_diff_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_diff * tree * coq_R_diff
        | R_diff_3 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_diff * tree * coq_R_diff
        
        type coq_R_union =
        | R_union_0 of tree * tree
        | R_union_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_union_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_union * tree * coq_R_union
       end
      
      module E : 
       sig 
        type t = TerminalOrderedType.Alt.t
        
        val compare :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
          comparison
        
        val eq_dec :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
       end
      
      type elt = TerminalOrderedType.Alt.t
      
      type t_ =
        Raw.t
        (* singleton inductive, whose constructor was Mkt *)
      
      val this : t_ -> Raw.t
      
      type t = t_
      
      val mem : elt -> t -> bool
      
      val add : elt -> t -> t
      
      val remove : elt -> t -> t
      
      val singleton : elt -> t
      
      val union : t -> t -> t
      
      val inter : t -> t -> t
      
      val diff : t -> t -> t
      
      val equal : t -> t -> bool
      
      val subset : t -> t -> bool
      
      val empty : t
      
      val is_empty : t -> bool
      
      val elements : t -> elt list
      
      val choose : t -> elt option
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val cardinal : t -> nat
      
      val filter : (elt -> bool) -> t -> t
      
      val for_all : (elt -> bool) -> t -> bool
      
      val exists_ : (elt -> bool) -> t -> bool
      
      val partition : (elt -> bool) -> t -> (t, t) prod
      
      val eq_dec : t -> t -> sumbool
      
      val compare : t -> t -> comparison
      
      val min_elt : t -> elt option
      
      val max_elt : t -> elt option
     end
    
    type elt = TerminalOrderedType.Alt.t
    
    type t = MSet.t
    
    val empty : t
    
    val is_empty : t -> bool
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val singleton : elt -> t
    
    val remove : elt -> t -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val eq_dec : t -> t -> sumbool
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val filter : (elt -> bool) -> t -> t
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val cardinal : t -> nat
    
    val elements : t -> elt list
    
    val choose : t -> elt option
    
    module MF : 
     sig 
      val eqb :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
     end
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
    
    val compare : t -> t -> t compare0
    
    module E : 
     sig 
      type t = TerminalOrderedType.Alt.t
      
      val compare :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
        TerminalOrderedType.Alt.t compare0
      
      val eq_dec :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
     end
   end
  
  module StateProdPosMap : 
   sig 
    module E : 
     sig 
      type t = StateProdPosOrderedType.Alt.t
      
      val compare :
        StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
        StateProdPosOrderedType.Alt.t compare0
      
      val eq_dec :
        StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
        sumbool
     end
    
    module Raw : 
     sig 
      type key = StateProdPosOrderedType.Alt.t
      
      type 'elt tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      
      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2
      
      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2
      
      val height : 'a1 tree -> Z_as_Int.t
      
      val cardinal : 'a1 tree -> nat
      
      val empty : 'a1 tree
      
      val is_empty : 'a1 tree -> bool
      
      val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool
      
      val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option
      
      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod
      
      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
      
      val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree
      
      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                           t_right : 'elt tree }
      
      val triple_rect :
        ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
      
      val triple_rec :
        ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
      
      val t_left : 'a1 triple -> 'a1 tree
      
      val t_opt : 'a1 triple -> 'a1 option
      
      val t_right : 'a1 triple -> 'a1 tree
      
      val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple
      
      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
      
      val elements_aux :
        (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
      
      val elements : 'a1 tree -> (key, 'a1) prod list
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      type 'elt enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration
      
      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2
      
      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2
      
      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
      
      val equal_more :
        ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 -> ('a1
        enumeration -> bool) -> 'a1 enumeration -> bool
      
      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool
      
      val equal_end : 'a1 enumeration -> bool
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
      
      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
      
      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
      
      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree
      
      module Proofs : 
       sig 
        module MX : 
         sig 
          module TO : 
           sig 
            type t = StateProdPosOrderedType.Alt.t
           end
          
          module IsTO : 
           sig 
            
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            sumbool
          
          val lt_dec :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            sumbool
          
          val eqb :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module TO : 
             sig 
              type t = StateProdPosOrderedType.Alt.t
             end
            
            module IsTO : 
             sig 
              
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> sumbool
            
            val lt_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> sumbool
            
            val eqb :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
           end
         end
        
        module L : 
         sig 
          module MX : 
           sig 
            module TO : 
             sig 
              type t = StateProdPosOrderedType.Alt.t
             end
            
            module IsTO : 
             sig 
              
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> sumbool
            
            val lt_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> sumbool
            
            val eqb :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
           end
          
          module PX : 
           sig 
            module MO : 
             sig 
              module TO : 
               sig 
                type t = StateProdPosOrderedType.Alt.t
               end
              
              module IsTO : 
               sig 
                
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> sumbool
              
              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> sumbool
              
              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end
           end
          
          type key = StateProdPosOrderedType.Alt.t
          
          type 'elt t = (StateProdPosOrderedType.Alt.t, 'elt) prod list
          
          val empty : 'a1 t
          
          val is_empty : 'a1 t -> bool
          
          val mem : key -> 'a1 t -> bool
          
          type 'elt coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
          | R_mem_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
          | R_mem_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list * bool
             * 'elt coq_R_mem
          
          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
            coq_R_mem -> 'a2
          
          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
            coq_R_mem -> 'a2
          
          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2
          
          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2
          
          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
          
          val find : key -> 'a1 t -> 'a1 option
          
          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
          | R_find_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
          | R_find_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 'elt option
             * 'elt coq_R_find
          
          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
            option -> 'a1 coq_R_find -> 'a2
          
          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
            option -> 'a1 coq_R_find -> 'a2
          
          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2
          
          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2
          
          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          
          val add : key -> 'a1 -> 'a1 t -> 'a1 t
          
          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
          | R_add_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
          | R_add_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 'elt t
             * 'elt coq_R_add
          
          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2
          
          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2
          
          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2
          
          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2
          
          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
          
          val remove : key -> 'a1 t -> 'a1 t
          
          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
          | R_remove_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
          | R_remove_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 'elt t
             * 'elt coq_R_remove
          
          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
            'a1 coq_R_remove -> 'a2
          
          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
            'a1 coq_R_remove -> 'a2
          
          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2
          
          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2
          
          val coq_R_remove_correct :
            key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          
          val elements : 'a1 t -> 'a1 t
          
          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
          
          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
          | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
             * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 'a
             * ('elt, 'a) coq_R_fold
          
          val coq_R_fold_rect :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
            ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
            -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
          
          val coq_R_fold_rec :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
            ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
            -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
          
          val fold_rect :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> 'a2 ->
            'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
          
          val fold_rec :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> 'a2 ->
            'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
          
          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold
          
          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
          
          type 'elt coq_R_equal =
          | R_equal_0 of 'elt t * 'elt t
          | R_equal_1 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
             * 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
             * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list * bool
             * 'elt coq_R_equal
          | R_equal_2 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
             * 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
             * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t, 'elt) prod list
             * StateProdPosOrderedType.Alt.t compare0
          | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
          
          val coq_R_equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
          
          val coq_R_equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
          
          val equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> 'a2
          
          val equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
            StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> 'a2
          
          val coq_R_equal_correct :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
          
          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
          
          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
          
          val option_cons :
            key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
          
          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
          
          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
          
          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t
          
          val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
          
          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
          
          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key, 'a3) prod list
          
          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
          
          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
        
        val coq_R_find_rec :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
        
        type 'elt coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
        
        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2
        
        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2
        
        type 'elt coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * Z_as_Int.t
           * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
           * 'elt tree * (key, 'elt) prod
        
        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
          'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1)
          prod) prod -> 'a1 coq_R_remove_min -> 'a2
        
        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
          'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1)
          prod) prod -> 'a1 coq_R_remove_min -> 'a2
        
        type 'elt coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key, 'elt) prod * key * 'elt
        
        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key -> 'a1
          -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_merge -> 'a2
        
        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key -> 'a1
          -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_merge -> 'a2
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
        
        val coq_R_remove_rec :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
        
        type 'elt coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key, 'elt) prod
        
        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
          'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
        
        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
          'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
        
        type 'elt coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        
        val coq_R_split_rect :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
          coq_R_split -> 'a2
        
        val coq_R_split_rec :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
          coq_R_split -> 'a2
        
        type ('elt, 'elt') coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
           * 'elt' tree * ('elt, 'elt') coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt' tree * ('elt, 'elt') coq_R_map_option
           * 'elt' tree * ('elt, 'elt') coq_R_map_option
        
        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3
        
        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3
        
        type ('elt, 'elt', 'elt'') coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'elt' tree
        | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * Z_as_Int.t
        | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt'
           * 'elt' tree * Z_as_Int.t * 'elt' tree * 'elt' option * 'elt' tree
           * 'elt'' * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt
           * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt'
           * 'elt' tree * Z_as_Int.t * 'elt' tree * 'elt' option * 'elt' tree
           * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
           * ('elt, 'elt', 'elt'') coq_R_map2_opt
        
        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4
        
        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4
        
        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
        
        val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
       end
     end
    
    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)
    
    val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
    
    val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
    
    val this : 'a1 bst -> 'a1 Raw.tree
    
    type 'elt t = 'elt bst
    
    type key = StateProdPosOrderedType.Alt.t
    
    val empty : 'a1 t
    
    val is_empty : 'a1 t -> bool
    
    val add : key -> 'a1 -> 'a1 t -> 'a1 t
    
    val remove : key -> 'a1 t -> 'a1 t
    
    val mem : key -> 'a1 t -> bool
    
    val find : key -> 'a1 t -> 'a1 option
    
    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
    
    val elements : 'a1 t -> (key, 'a1) prod list
    
    val cardinal : 'a1 t -> nat
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end
  
  val nullable_symb : A.Gram.symbol -> bool
  
  val nullable_word : A.Gram.symbol list -> bool
  
  val first_nterm_set : A.Gram.nonterminal -> TerminalSet.t
  
  val first_symb_set : A.Gram.symbol -> TerminalSet.t
  
  val first_word_set : A.Gram.symbol list -> TerminalSet.t
  
  val future_of_prod : A.Gram.production -> nat -> A.Gram.symbol list
  
  val items_map : unit0 -> TerminalSet.t StateProdPosMap.t
  
  val find_items_map :
    TerminalSet.t StateProdPosMap.t -> A.state -> A.Gram.production -> nat ->
    TerminalSet.t
  
  val forallb_items :
    TerminalSet.t StateProdPosMap.t -> (A.state -> A.Gram.production -> nat
    -> TerminalSet.t -> bool) -> bool
  
  val is_nullable_stable : unit0 -> bool
  
  val is_first_stable : unit0 -> bool
  
  val is_start_future : TerminalSet.t StateProdPosMap.t -> bool
  
  val is_terminal_shift : TerminalSet.t StateProdPosMap.t -> bool
  
  val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool
  
  val is_non_terminal_goto : TerminalSet.t StateProdPosMap.t -> bool
  
  val is_start_goto : unit0 -> bool
  
  val is_non_terminal_closed : TerminalSet.t StateProdPosMap.t -> bool
  
  val is_complete : unit0 -> bool
 end

module Coq5_Make : 
 functor (A:Coq_T) ->
 functor (Inter:sig 
  type 'a result =
  | Err
  | OK of 'a
  
  val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
  
  val bind2 :
    ('a1, 'a2) prod result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
  
  val app_str : 'a1 list -> 'a1 stream -> 'a1 stream
  
  type noninitstate_type = A.Gram.symbol_semantic_type
  
  type stack = (A.noninitstate, noninitstate_type) sigT list
  
  val state_of_stack : A.initstate -> stack -> A.state
  
  val pop :
    A.Gram.symbol list -> stack -> 'a1 arrows_right -> (stack, 'a1) prod
    result
  
  type step_result =
  | Fail_sr
  | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token stream
  | Progress_sr of stack * A.GramDefs.token stream
  
  val step_result_rect :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    stream -> 'a1) -> (stack -> A.GramDefs.token stream -> 'a1) ->
    step_result -> 'a1
  
  val step_result_rec :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    stream -> 'a1) -> (stack -> A.GramDefs.token stream -> 'a1) ->
    step_result -> 'a1
  
  val prod_action' :
    A.Gram.production -> A.Gram.symbol_semantic_type arrows_right
  
  val reduce_step :
    A.initstate -> stack -> A.Gram.production -> A.GramDefs.token stream ->
    step_result result
  
  val step :
    A.initstate -> stack -> A.GramDefs.token stream -> step_result result
  
  type parse_result =
  | Fail_pr
  | Timeout_pr
  | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token stream
  
  val parse_result_rect :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
  
  val parse_result_rec :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
  
  val parse_fix :
    A.initstate -> stack -> A.GramDefs.token stream -> nat -> parse_result
    result
  
  val parse :
    A.initstate -> A.GramDefs.token stream -> nat -> parse_result result
 end) ->
 sig 
  module Valid : 
   sig 
    module TerminalComparableM : 
     sig 
      type t = A.Gram.terminal
      
      val tComparable : t comparable
     end
    
    module TerminalOrderedType : 
     sig 
      module Alt : 
       sig 
        type t = TerminalComparableM.t
        
        val compare : t -> t -> comparison
       end
      
      type t = Alt.t
      
      val compare : Alt.t -> Alt.t -> Alt.t compare0
      
      val eq_dec : Alt.t -> Alt.t -> sumbool
     end
    
    module StateProdPosComparableM : 
     sig 
      type t = ((A.state, A.Gram.production) prod, nat) prod
      
      val tComparable : t comparable
     end
    
    module StateProdPosOrderedType : 
     sig 
      module Alt : 
       sig 
        type t = StateProdPosComparableM.t
        
        val compare : t -> t -> comparison
       end
      
      type t = Alt.t
      
      val compare : Alt.t -> Alt.t -> Alt.t compare0
      
      val eq_dec : Alt.t -> Alt.t -> sumbool
     end
    
    module TerminalSet : 
     sig 
      module X' : 
       sig 
        type t = TerminalOrderedType.Alt.t
        
        val eq_dec :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
        
        val compare :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
          comparison
       end
      
      module MSet : 
       sig 
        module Raw : 
         sig 
          type elt = TerminalOrderedType.Alt.t
          
          type tree =
          | Leaf
          | Node of Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree
          
          val empty : tree
          
          val is_empty : tree -> bool
          
          val mem : TerminalOrderedType.Alt.t -> tree -> bool
          
          val min_elt : tree -> elt option
          
          val max_elt : tree -> elt option
          
          val choose : tree -> elt option
          
          val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
          
          val elements_aux :
            TerminalOrderedType.Alt.t list -> tree ->
            TerminalOrderedType.Alt.t list
          
          val elements : tree -> TerminalOrderedType.Alt.t list
          
          val rev_elements_aux :
            TerminalOrderedType.Alt.t list -> tree ->
            TerminalOrderedType.Alt.t list
          
          val rev_elements : tree -> TerminalOrderedType.Alt.t list
          
          val cardinal : tree -> nat
          
          val maxdepth : tree -> nat
          
          val mindepth : tree -> nat
          
          val for_all : (elt -> bool) -> tree -> bool
          
          val exists_ : (elt -> bool) -> tree -> bool
          
          type enumeration =
          | End
          | More of elt * tree * enumeration
          
          val cons : tree -> enumeration -> enumeration
          
          val compare_more :
            TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
            enumeration -> comparison
          
          val compare_cont :
            tree -> (enumeration -> comparison) -> enumeration -> comparison
          
          val compare_end : enumeration -> comparison
          
          val compare : tree -> tree -> comparison
          
          val equal : tree -> tree -> bool
          
          val subsetl :
            (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
          
          val subsetr :
            (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
          
          val subset : tree -> tree -> bool
          
          type t = tree
          
          val height : t -> Z_as_Int.t
          
          val singleton : TerminalOrderedType.Alt.t -> tree
          
          val create : t -> TerminalOrderedType.Alt.t -> t -> tree
          
          val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree
          
          val bal : t -> TerminalOrderedType.Alt.t -> t -> tree
          
          val add : TerminalOrderedType.Alt.t -> tree -> tree
          
          val join : tree -> elt -> t -> t
          
          val remove_min : tree -> elt -> t -> (t, elt) prod
          
          val merge : tree -> tree -> tree
          
          val remove : TerminalOrderedType.Alt.t -> tree -> tree
          
          val concat : tree -> tree -> tree
          
          type triple = { t_left : t; t_in : bool; t_right : t }
          
          val t_left : triple -> t
          
          val t_in : triple -> bool
          
          val t_right : triple -> t
          
          val split : TerminalOrderedType.Alt.t -> tree -> triple
          
          val inter : tree -> tree -> tree
          
          val diff : tree -> tree -> tree
          
          val union : tree -> tree -> tree
          
          val filter : (elt -> bool) -> tree -> tree
          
          val partition : (elt -> bool) -> t -> (t, t) prod
          
          val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool
          
          val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool
          
          val isok : tree -> bool
          
          module MX : 
           sig 
            module OrderTac : 
             sig 
              module OTF : 
               sig 
                type t = TerminalOrderedType.Alt.t
                
                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  sumbool
               end
              
              module TO : 
               sig 
                type t = TerminalOrderedType.Alt.t
                
                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  sumbool
               end
             end
            
            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              sumbool
            
            val lt_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              sumbool
            
            val eqb :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end
          
          type coq_R_min_elt =
          | R_min_elt_0 of tree
          | R_min_elt_1 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_min_elt_2 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * elt option * coq_R_min_elt
          
          type coq_R_max_elt =
          | R_max_elt_0 of tree
          | R_max_elt_1 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_max_elt_2 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * elt option * coq_R_max_elt
          
          module L : 
           sig 
            module MO : 
             sig 
              module OrderTac : 
               sig 
                module OTF : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    sumbool
                 end
                
                module TO : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    sumbool
                 end
               end
              
              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                sumbool
              
              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                sumbool
              
              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
             end
           end
          
          val flatten_e : enumeration -> elt list
          
          type coq_R_bal =
          | R_bal_0 of t * TerminalOrderedType.Alt.t * t
          | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_bal_4 of t * TerminalOrderedType.Alt.t * t
          | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_bal_8 of t * TerminalOrderedType.Alt.t * t
          
          type coq_R_remove_min =
          | R_remove_min_0 of tree * elt * t
          | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * (t, elt) prod
             * coq_R_remove_min * t * elt
          
          type coq_R_merge =
          | R_merge_0 of tree * tree
          | R_merge_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_merge_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * elt
          
          type coq_R_concat =
          | R_concat_0 of tree * tree
          | R_concat_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_concat_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * elt
          
          type coq_R_inter =
          | R_inter_0 of tree * tree
          | R_inter_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_inter_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_inter * tree * coq_R_inter
          | R_inter_3 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_inter * tree * coq_R_inter
          
          type coq_R_diff =
          | R_diff_0 of tree * tree
          | R_diff_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_diff_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_diff * tree * coq_R_diff
          | R_diff_3 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_diff * tree * coq_R_diff
          
          type coq_R_union =
          | R_union_0 of tree * tree
          | R_union_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_union_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_union * tree * coq_R_union
         end
        
        module E : 
         sig 
          type t = TerminalOrderedType.Alt.t
          
          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
         end
        
        type elt = TerminalOrderedType.Alt.t
        
        type t_ =
          Raw.t
          (* singleton inductive, whose constructor was Mkt *)
        
        val this : t_ -> Raw.t
        
        type t = t_
        
        val mem : elt -> t -> bool
        
        val add : elt -> t -> t
        
        val remove : elt -> t -> t
        
        val singleton : elt -> t
        
        val union : t -> t -> t
        
        val inter : t -> t -> t
        
        val diff : t -> t -> t
        
        val equal : t -> t -> bool
        
        val subset : t -> t -> bool
        
        val empty : t
        
        val is_empty : t -> bool
        
        val elements : t -> elt list
        
        val choose : t -> elt option
        
        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
        
        val cardinal : t -> nat
        
        val filter : (elt -> bool) -> t -> t
        
        val for_all : (elt -> bool) -> t -> bool
        
        val exists_ : (elt -> bool) -> t -> bool
        
        val partition : (elt -> bool) -> t -> (t, t) prod
        
        val eq_dec : t -> t -> sumbool
        
        val compare : t -> t -> comparison
        
        val min_elt : t -> elt option
        
        val max_elt : t -> elt option
       end
      
      type elt = TerminalOrderedType.Alt.t
      
      type t = MSet.t
      
      val empty : t
      
      val is_empty : t -> bool
      
      val mem : elt -> t -> bool
      
      val add : elt -> t -> t
      
      val singleton : elt -> t
      
      val remove : elt -> t -> t
      
      val union : t -> t -> t
      
      val inter : t -> t -> t
      
      val diff : t -> t -> t
      
      val eq_dec : t -> t -> sumbool
      
      val equal : t -> t -> bool
      
      val subset : t -> t -> bool
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val for_all : (elt -> bool) -> t -> bool
      
      val exists_ : (elt -> bool) -> t -> bool
      
      val filter : (elt -> bool) -> t -> t
      
      val partition : (elt -> bool) -> t -> (t, t) prod
      
      val cardinal : t -> nat
      
      val elements : t -> elt list
      
      val choose : t -> elt option
      
      module MF : 
       sig 
        val eqb :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
       end
      
      val min_elt : t -> elt option
      
      val max_elt : t -> elt option
      
      val compare : t -> t -> t compare0
      
      module E : 
       sig 
        type t = TerminalOrderedType.Alt.t
        
        val compare :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
          TerminalOrderedType.Alt.t compare0
        
        val eq_dec :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
       end
     end
    
    module StateProdPosMap : 
     sig 
      module E : 
       sig 
        type t = StateProdPosOrderedType.Alt.t
        
        val compare :
          StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
          StateProdPosOrderedType.Alt.t compare0
        
        val eq_dec :
          StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
          sumbool
       end
      
      module Raw : 
       sig 
        type key = StateProdPosOrderedType.Alt.t
        
        type 'elt tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
        
        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2
        
        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2
        
        val height : 'a1 tree -> Z_as_Int.t
        
        val cardinal : 'a1 tree -> nat
        
        val empty : 'a1 tree
        
        val is_empty : 'a1 tree -> bool
        
        val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool
        
        val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option
        
        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
          prod
        
        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
        
        val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree
        
        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                             t_right : 'elt tree }
        
        val triple_rect :
          ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
        
        val triple_rec :
          ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
        
        val t_left : 'a1 triple -> 'a1 tree
        
        val t_opt : 'a1 triple -> 'a1 option
        
        val t_right : 'a1 triple -> 'a1 tree
        
        val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple
        
        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
        
        val elements_aux :
          (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
        
        val elements : 'a1 tree -> (key, 'a1) prod list
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
        
        type 'elt enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration
        
        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2
        
        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2
        
        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
        
        val equal_more :
          ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 ->
          ('a1 enumeration -> bool) -> 'a1 enumeration -> bool
        
        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool
        
        val equal_end : 'a1 enumeration -> bool
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
        
        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
        
        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
        
        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree
        
        module Proofs : 
         sig 
          module MX : 
           sig 
            module TO : 
             sig 
              type t = StateProdPosOrderedType.Alt.t
             end
            
            module IsTO : 
             sig 
              
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> sumbool
            
            val lt_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> sumbool
            
            val eqb :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
           end
          
          module PX : 
           sig 
            module MO : 
             sig 
              module TO : 
               sig 
                type t = StateProdPosOrderedType.Alt.t
               end
              
              module IsTO : 
               sig 
                
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> sumbool
              
              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> sumbool
              
              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end
           end
          
          module L : 
           sig 
            module MX : 
             sig 
              module TO : 
               sig 
                type t = StateProdPosOrderedType.Alt.t
               end
              
              module IsTO : 
               sig 
                
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> sumbool
              
              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> sumbool
              
              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end
            
            module PX : 
             sig 
              module MO : 
               sig 
                module TO : 
                 sig 
                  type t = StateProdPosOrderedType.Alt.t
                 end
                
                module IsTO : 
                 sig 
                  
                 end
                
                module OrderTac : 
                 sig 
                  
                 end
                
                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> sumbool
                
                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> sumbool
                
                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end
             end
            
            type key = StateProdPosOrderedType.Alt.t
            
            type 'elt t = (StateProdPosOrderedType.Alt.t, 'elt) prod list
            
            val empty : 'a1 t
            
            val is_empty : 'a1 t -> bool
            
            val mem : key -> 'a1 t -> bool
            
            type 'elt coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list
            | R_mem_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list
            | R_mem_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list * bool
               * 'elt coq_R_mem
            
            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
              'a1 coq_R_mem -> 'a2
            
            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
              'a1 coq_R_mem -> 'a2
            
            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
            
            val find : key -> 'a1 t -> 'a1 option
            
            type 'elt coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list
            | R_find_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list
            | R_find_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list
               * 'elt option * 'elt coq_R_find
            
            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
              'a1 option -> 'a1 coq_R_find -> 'a2
            
            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
              'a1 option -> 'a1 coq_R_find -> 'a2
            
            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
            
            val add : key -> 'a1 -> 'a1 t -> 'a1 t
            
            type 'elt coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list
            | R_add_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list
            | R_add_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 'elt t
               * 'elt coq_R_add
            
            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
              -> 'a1 coq_R_add -> 'a2
            
            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
              -> 'a1 coq_R_add -> 'a2
            
            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
            
            val remove : key -> 'a1 t -> 'a1 t
            
            type 'elt coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
            | R_remove_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
            | R_remove_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
               * 'elt t * 'elt coq_R_remove
            
            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1
              t -> 'a1 coq_R_remove -> 'a2
            
            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1
              t -> 'a1 coq_R_remove -> 'a2
            
            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            
            val elements : 'a1 t -> 'a1 t
            
            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
            
            type ('elt, 'a) coq_R_fold =
            | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
            | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
               * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 'a
               * ('elt, 'a) coq_R_fold
            
            val coq_R_fold_rect :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 ->
              'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
            
            val coq_R_fold_rec :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 ->
              'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
            
            val fold_rect :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> 'a2 ->
              'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
            
            val fold_rec :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> 'a2 ->
              'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
            
            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold
            
            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
            
            type 'elt coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
               * 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
               * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list * bool
               * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
               * 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
               * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t, 'elt) prod list
               * StateProdPosOrderedType.Alt.t compare0
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
            
            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
              -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
              'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
            
            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
              -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
              'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
            
            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
              'a1 t -> 'a1 t -> 'a2
            
            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
              __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
              StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
              'a1 t -> 'a1 t -> 'a2
            
            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal
            
            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
            
            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
            
            val option_cons :
              key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod
              list
            
            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
            
            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
            
            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t
            
            val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
            
            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 ->
              'a3
            
            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key, 'a3) prod list
            
            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod
              option
            
            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end
          
          type 'elt coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          
          val coq_R_mem_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
            'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
          
          val coq_R_mem_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
            'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
          
          type 'elt coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          
          val coq_R_find_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
            coq_R_find -> 'a2
          
          val coq_R_find_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
            coq_R_find -> 'a2
          
          type 'elt coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
          
          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
          
          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
          
          type 'elt coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          
          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
          
          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
          
          type 'elt coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
             * 'elt tree * (key, 'elt) prod
          
          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
            'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key,
            'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
          
          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
            'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key,
            'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
          
          type 'elt coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key, 'elt) prod * key * 'elt
          
          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key ->
            'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2
          
          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key ->
            'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2
          
          type 'elt coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          
          val coq_R_remove_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2
          
          val coq_R_remove_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2
          
          type 'elt coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key, 'elt) prod
          
          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
            'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
          
          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
            'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
          
          type 'elt coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          
          val coq_R_split_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
            'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1
            tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
            triple -> 'a1 coq_R_split -> 'a2
          
          val coq_R_split_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
            'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1
            tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
            triple -> 'a1 coq_R_split -> 'a2
          
          type ('elt, 'elt') coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt' * 'elt' tree
             * ('elt, 'elt') coq_R_map_option * 'elt' tree
             * ('elt, 'elt') coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt' tree * ('elt, 'elt') coq_R_map_option
             * 'elt' tree * ('elt, 'elt') coq_R_map_option
          
          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3
          
          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3
          
          type ('elt, 'elt', 'elt'') coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'elt' tree
          | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt'
             * 'elt' tree * Z_as_Int.t * 'elt' tree * 'elt' option
             * 'elt' tree * 'elt'' * 'elt'' tree
             * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
             * ('elt, 'elt', 'elt'') coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt'
             * 'elt' tree * Z_as_Int.t * 'elt' tree * 'elt' option
             * 'elt' tree * 'elt'' tree
             * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
             * ('elt, 'elt', 'elt'') coq_R_map2_opt
          
          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
          
          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
          
          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
          
          val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
         end
       end
      
      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)
      
      val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
      
      val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
      
      val this : 'a1 bst -> 'a1 Raw.tree
      
      type 'elt t = 'elt bst
      
      type key = StateProdPosOrderedType.Alt.t
      
      val empty : 'a1 t
      
      val is_empty : 'a1 t -> bool
      
      val add : key -> 'a1 -> 'a1 t -> 'a1 t
      
      val remove : key -> 'a1 t -> 'a1 t
      
      val mem : key -> 'a1 t -> bool
      
      val find : key -> 'a1 t -> 'a1 option
      
      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
      
      val elements : 'a1 t -> (key, 'a1) prod list
      
      val cardinal : 'a1 t -> nat
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end
    
    val nullable_symb : A.Gram.symbol -> bool
    
    val nullable_word : A.Gram.symbol list -> bool
    
    val first_nterm_set : A.Gram.nonterminal -> TerminalSet.t
    
    val first_symb_set : A.Gram.symbol -> TerminalSet.t
    
    val first_word_set : A.Gram.symbol list -> TerminalSet.t
    
    val future_of_prod : A.Gram.production -> nat -> A.Gram.symbol list
    
    val items_map : unit0 -> TerminalSet.t StateProdPosMap.t
    
    val find_items_map :
      TerminalSet.t StateProdPosMap.t -> A.state -> A.Gram.production -> nat
      -> TerminalSet.t
    
    val forallb_items :
      TerminalSet.t StateProdPosMap.t -> (A.state -> A.Gram.production -> nat
      -> TerminalSet.t -> bool) -> bool
    
    val is_nullable_stable : unit0 -> bool
    
    val is_first_stable : unit0 -> bool
    
    val is_start_future : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_terminal_shift : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_non_terminal_goto : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_start_goto : unit0 -> bool
    
    val is_non_terminal_closed : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_complete : unit0 -> bool
   end
  
  type pt_zipper =
  | Top_ptz
  | Cons_ptl_ptz of A.Gram.symbol * A.GramDefs.token list
     * A.Gram.symbol_semantic_type * A.Gram.symbol list
     * A.GramDefs.token list * tuple * A.GramDefs.parse_tree_list
     * ptl_zipper
  and ptl_zipper =
  | Non_terminal_pt_ptlz of A.Gram.production * A.GramDefs.token list * 
     tuple * pt_zipper
  | Cons_ptl_ptlz of A.Gram.symbol * A.GramDefs.token list
     * A.Gram.symbol_semantic_type * A.GramDefs.parse_tree
     * A.Gram.symbol list * A.GramDefs.token list * tuple * ptl_zipper
  
  val pt_zipper_rect :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    'a1 -> (A.Gram.symbol -> A.GramDefs.token list ->
    A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
    list -> tuple -> A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) ->
    A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_zipper -> 'a1
  
  val pt_zipper_rec :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    'a1 -> (A.Gram.symbol -> A.GramDefs.token list ->
    A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
    list -> tuple -> A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) ->
    A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_zipper -> 'a1
  
  val ptl_zipper_rect :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    (A.Gram.production -> A.GramDefs.token list -> tuple -> pt_zipper -> 'a1)
    -> (A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type
    -> A.GramDefs.parse_tree -> A.Gram.symbol list -> A.GramDefs.token list
    -> tuple -> ptl_zipper -> 'a1 -> 'a1) -> A.Gram.symbol list ->
    A.GramDefs.token list -> tuple -> ptl_zipper -> 'a1
  
  val ptl_zipper_rec :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    (A.Gram.production -> A.GramDefs.token list -> tuple -> pt_zipper -> 'a1)
    -> (A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type
    -> A.GramDefs.parse_tree -> A.Gram.symbol list -> A.GramDefs.token list
    -> tuple -> ptl_zipper -> 'a1 -> 'a1) -> A.Gram.symbol list ->
    A.GramDefs.token list -> tuple -> ptl_zipper -> 'a1
  
  val ptlz_cost :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper -> nat
  
  val ptz_cost :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_zipper -> nat
  
  type pt_dot =
  | Reduce_ptd of ptl_zipper
  | Shift_ptd of A.Gram.terminal * A.Gram.symbol_semantic_type
     * A.Gram.symbol list * A.GramDefs.token list * tuple
     * A.GramDefs.parse_tree_list * ptl_zipper
  
  val pt_dot_rect :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    (ptl_zipper -> 'a1) -> (A.Gram.terminal -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
    A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1
  
  val pt_dot_rec :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    (ptl_zipper -> 'a1) -> (A.Gram.terminal -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
    A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1
  
  val ptd_cost :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_dot -> nat
  
  val ptlz_buffer :
    A.initstate -> A.GramDefs.token list -> A.GramDefs.token stream ->
    A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
    list -> tuple -> ptl_zipper -> A.GramDefs.token stream
  
  val ptz_buffer :
    A.initstate -> A.GramDefs.token list -> A.GramDefs.token stream ->
    A.Gram.symbol_semantic_type -> A.Gram.symbol -> A.GramDefs.token list ->
    A.Gram.symbol_semantic_type -> pt_zipper -> A.GramDefs.token stream
  
  val ptd_buffer :
    A.initstate -> A.GramDefs.token list -> A.GramDefs.token stream ->
    A.Gram.symbol_semantic_type -> pt_dot -> A.GramDefs.token stream
  
  val ptlz_prod :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
    A.Gram.production
  
  val ptlz_past :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
    A.Gram.symbol list
  
  val build_pt_dot :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
    A.GramDefs.parse_tree_list -> ptl_zipper -> pt_dot
  
  val pop_ptlz :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
    A.GramDefs.parse_tree_list -> ptl_zipper -> (A.GramDefs.token list,
    (A.Gram.symbol_semantic_type, (pt_zipper, A.GramDefs.parse_tree) prod)
    sigT) sigT
  
  val next_ptd :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_dot -> pt_dot option
  
  val init_ptd :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.GramDefs.parse_tree -> pt_dot
 end

module Coq6_Make : 
 functor (Aut:Coq_T) ->
 sig 
  module Inter : 
   sig 
    type 'a result =
    | Err
    | OK of 'a
    
    val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
    
    val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
    
    val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
    
    val bind2 :
      ('a1, 'a2) prod result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
    
    val app_str : 'a1 list -> 'a1 stream -> 'a1 stream
    
    type noninitstate_type = Aut.Gram.symbol_semantic_type
    
    type stack = (Aut.noninitstate, noninitstate_type) sigT list
    
    val state_of_stack : Aut.initstate -> stack -> Aut.state
    
    val pop :
      Aut.Gram.symbol list -> stack -> 'a1 arrows_right -> (stack, 'a1) prod
      result
    
    type step_result =
    | Fail_sr
    | Accept_sr of Aut.Gram.symbol_semantic_type * Aut.GramDefs.token stream
    | Progress_sr of stack * Aut.GramDefs.token stream
    
    val step_result_rect :
      Aut.initstate -> 'a1 -> (Aut.Gram.symbol_semantic_type ->
      Aut.GramDefs.token stream -> 'a1) -> (stack -> Aut.GramDefs.token
      stream -> 'a1) -> step_result -> 'a1
    
    val step_result_rec :
      Aut.initstate -> 'a1 -> (Aut.Gram.symbol_semantic_type ->
      Aut.GramDefs.token stream -> 'a1) -> (stack -> Aut.GramDefs.token
      stream -> 'a1) -> step_result -> 'a1
    
    val prod_action' :
      Aut.Gram.production -> Aut.Gram.symbol_semantic_type arrows_right
    
    val reduce_step :
      Aut.initstate -> stack -> Aut.Gram.production -> Aut.GramDefs.token
      stream -> step_result result
    
    val step :
      Aut.initstate -> stack -> Aut.GramDefs.token stream -> step_result
      result
    
    type parse_result =
    | Fail_pr
    | Timeout_pr
    | Parsed_pr of Aut.Gram.symbol_semantic_type * Aut.GramDefs.token stream
    
    val parse_result_rect :
      Aut.initstate -> 'a1 -> 'a1 -> (Aut.Gram.symbol_semantic_type ->
      Aut.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
    
    val parse_result_rec :
      Aut.initstate -> 'a1 -> 'a1 -> (Aut.Gram.symbol_semantic_type ->
      Aut.GramDefs.token stream -> 'a1) -> parse_result -> 'a1
    
    val parse_fix :
      Aut.initstate -> stack -> Aut.GramDefs.token stream -> nat ->
      parse_result result
    
    val parse :
      Aut.initstate -> Aut.GramDefs.token stream -> nat -> parse_result
      result
   end
  
  module Safe : 
   sig 
    module Valid : 
     sig 
      val singleton_state_pred : Aut.state -> Aut.state -> bool
      
      val past_state_of_state : Aut.state -> (Aut.state -> bool) list
      
      val head_symbs_of_state : Aut.state -> Aut.Gram.symbol list
      
      val head_states_of_state : Aut.state -> (Aut.state -> bool) list
      
      val is_prefix : Aut.Gram.symbol list -> Aut.Gram.symbol list -> bool
      
      val is_shift_head_symbs : unit0 -> bool
      
      val is_goto_head_symbs : unit0 -> bool
      
      val is_prefix_pred :
        (Aut.state -> bool) list -> (Aut.state -> bool) list -> bool
      
      val is_shift_past_state : unit0 -> bool
      
      val is_goto_past_state : unit0 -> bool
      
      val is_state_valid_after_pop :
        Aut.state -> Aut.Gram.symbol list -> (Aut.state -> bool) list -> bool
      
      val is_valid_for_reduce : Aut.state -> Aut.Gram.production -> bool
      
      val is_reduce_ok : unit0 -> bool
      
      val is_safe : unit0 -> bool
     end
    
    val state_stack_of_stack :
      Aut.initstate -> Inter.stack -> (Aut.state -> bool) list
    
    val symb_stack_of_stack : Inter.stack -> Aut.Gram.symbol list
    
    val internal_eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
    
    val parse_with_safe :
      Aut.initstate -> Aut.GramDefs.token stream -> nat -> Inter.parse_result
   end
  
  module Correct : 
   sig 
    val internal_eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
   end
  
  module Complete : 
   sig 
    module Valid : 
     sig 
      module TerminalComparableM : 
       sig 
        type t = Aut.Gram.terminal
        
        val tComparable : t comparable
       end
      
      module TerminalOrderedType : 
       sig 
        module Alt : 
         sig 
          type t = TerminalComparableM.t
          
          val compare : t -> t -> comparison
         end
        
        type t = Alt.t
        
        val compare : Alt.t -> Alt.t -> Alt.t compare0
        
        val eq_dec : Alt.t -> Alt.t -> sumbool
       end
      
      module StateProdPosComparableM : 
       sig 
        type t = ((Aut.state, Aut.Gram.production) prod, nat) prod
        
        val tComparable : t comparable
       end
      
      module StateProdPosOrderedType : 
       sig 
        module Alt : 
         sig 
          type t = StateProdPosComparableM.t
          
          val compare : t -> t -> comparison
         end
        
        type t = Alt.t
        
        val compare : Alt.t -> Alt.t -> Alt.t compare0
        
        val eq_dec : Alt.t -> Alt.t -> sumbool
       end
      
      module TerminalSet : 
       sig 
        module X' : 
         sig 
          type t = TerminalOrderedType.Alt.t
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
          
          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison
         end
        
        module MSet : 
         sig 
          module Raw : 
           sig 
            type elt = TerminalOrderedType.Alt.t
            
            type tree =
            | Leaf
            | Node of Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree
            
            val empty : tree
            
            val is_empty : tree -> bool
            
            val mem : TerminalOrderedType.Alt.t -> tree -> bool
            
            val min_elt : tree -> elt option
            
            val max_elt : tree -> elt option
            
            val choose : tree -> elt option
            
            val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
            
            val elements_aux :
              TerminalOrderedType.Alt.t list -> tree ->
              TerminalOrderedType.Alt.t list
            
            val elements : tree -> TerminalOrderedType.Alt.t list
            
            val rev_elements_aux :
              TerminalOrderedType.Alt.t list -> tree ->
              TerminalOrderedType.Alt.t list
            
            val rev_elements : tree -> TerminalOrderedType.Alt.t list
            
            val cardinal : tree -> nat
            
            val maxdepth : tree -> nat
            
            val mindepth : tree -> nat
            
            val for_all : (elt -> bool) -> tree -> bool
            
            val exists_ : (elt -> bool) -> tree -> bool
            
            type enumeration =
            | End
            | More of elt * tree * enumeration
            
            val cons : tree -> enumeration -> enumeration
            
            val compare_more :
              TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
              enumeration -> comparison
            
            val compare_cont :
              tree -> (enumeration -> comparison) -> enumeration ->
              comparison
            
            val compare_end : enumeration -> comparison
            
            val compare : tree -> tree -> comparison
            
            val equal : tree -> tree -> bool
            
            val subsetl :
              (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
            
            val subsetr :
              (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
            
            val subset : tree -> tree -> bool
            
            type t = tree
            
            val height : t -> Z_as_Int.t
            
            val singleton : TerminalOrderedType.Alt.t -> tree
            
            val create : t -> TerminalOrderedType.Alt.t -> t -> tree
            
            val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree
            
            val bal : t -> TerminalOrderedType.Alt.t -> t -> tree
            
            val add : TerminalOrderedType.Alt.t -> tree -> tree
            
            val join : tree -> elt -> t -> t
            
            val remove_min : tree -> elt -> t -> (t, elt) prod
            
            val merge : tree -> tree -> tree
            
            val remove : TerminalOrderedType.Alt.t -> tree -> tree
            
            val concat : tree -> tree -> tree
            
            type triple = { t_left : t; t_in : bool; t_right : t }
            
            val t_left : triple -> t
            
            val t_in : triple -> bool
            
            val t_right : triple -> t
            
            val split : TerminalOrderedType.Alt.t -> tree -> triple
            
            val inter : tree -> tree -> tree
            
            val diff : tree -> tree -> tree
            
            val union : tree -> tree -> tree
            
            val filter : (elt -> bool) -> tree -> tree
            
            val partition : (elt -> bool) -> t -> (t, t) prod
            
            val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool
            
            val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool
            
            val isok : tree -> bool
            
            module MX : 
             sig 
              module OrderTac : 
               sig 
                module OTF : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    sumbool
                 end
                
                module TO : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    sumbool
                 end
               end
              
              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                sumbool
              
              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                sumbool
              
              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
             end
            
            type coq_R_min_elt =
            | R_min_elt_0 of tree
            | R_min_elt_1 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_min_elt_2 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * elt option
               * coq_R_min_elt
            
            type coq_R_max_elt =
            | R_max_elt_0 of tree
            | R_max_elt_1 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_max_elt_2 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * elt option
               * coq_R_max_elt
            
            module L : 
             sig 
              module MO : 
               sig 
                module OrderTac : 
                 sig 
                  module OTF : 
                   sig 
                    type t = TerminalOrderedType.Alt.t
                    
                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison
                    
                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> sumbool
                   end
                  
                  module TO : 
                   sig 
                    type t = TerminalOrderedType.Alt.t
                    
                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison
                    
                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> sumbool
                   end
                 end
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  sumbool
                
                val lt_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  sumbool
                
                val eqb :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end
            
            val flatten_e : enumeration -> elt list
            
            type coq_R_bal =
            | R_bal_0 of t * TerminalOrderedType.Alt.t * t
            | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree
            | R_bal_4 of t * TerminalOrderedType.Alt.t * t
            | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree
            | R_bal_8 of t * TerminalOrderedType.Alt.t * t
            
            type coq_R_remove_min =
            | R_remove_min_0 of tree * elt * t
            | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * (t, elt) prod
               * coq_R_remove_min * t * elt
            
            type coq_R_merge =
            | R_merge_0 of tree * tree
            | R_merge_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_merge_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * elt
            
            type coq_R_concat =
            | R_concat_0 of tree * tree
            | R_concat_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_concat_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * elt
            
            type coq_R_inter =
            | R_inter_0 of tree * tree
            | R_inter_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_inter_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_inter * tree * coq_R_inter
            | R_inter_3 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_inter * tree * coq_R_inter
            
            type coq_R_diff =
            | R_diff_0 of tree * tree
            | R_diff_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_diff_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_diff * tree * coq_R_diff
            | R_diff_3 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_diff * tree * coq_R_diff
            
            type coq_R_union =
            | R_union_0 of tree * tree
            | R_union_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_union_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_union * tree * coq_R_union
           end
          
          module E : 
           sig 
            type t = TerminalOrderedType.Alt.t
            
            val compare :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              comparison
            
            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              sumbool
           end
          
          type elt = TerminalOrderedType.Alt.t
          
          type t_ =
            Raw.t
            (* singleton inductive, whose constructor was Mkt *)
          
          val this : t_ -> Raw.t
          
          type t = t_
          
          val mem : elt -> t -> bool
          
          val add : elt -> t -> t
          
          val remove : elt -> t -> t
          
          val singleton : elt -> t
          
          val union : t -> t -> t
          
          val inter : t -> t -> t
          
          val diff : t -> t -> t
          
          val equal : t -> t -> bool
          
          val subset : t -> t -> bool
          
          val empty : t
          
          val is_empty : t -> bool
          
          val elements : t -> elt list
          
          val choose : t -> elt option
          
          val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
          
          val cardinal : t -> nat
          
          val filter : (elt -> bool) -> t -> t
          
          val for_all : (elt -> bool) -> t -> bool
          
          val exists_ : (elt -> bool) -> t -> bool
          
          val partition : (elt -> bool) -> t -> (t, t) prod
          
          val eq_dec : t -> t -> sumbool
          
          val compare : t -> t -> comparison
          
          val min_elt : t -> elt option
          
          val max_elt : t -> elt option
         end
        
        type elt = TerminalOrderedType.Alt.t
        
        type t = MSet.t
        
        val empty : t
        
        val is_empty : t -> bool
        
        val mem : elt -> t -> bool
        
        val add : elt -> t -> t
        
        val singleton : elt -> t
        
        val remove : elt -> t -> t
        
        val union : t -> t -> t
        
        val inter : t -> t -> t
        
        val diff : t -> t -> t
        
        val eq_dec : t -> t -> sumbool
        
        val equal : t -> t -> bool
        
        val subset : t -> t -> bool
        
        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
        
        val for_all : (elt -> bool) -> t -> bool
        
        val exists_ : (elt -> bool) -> t -> bool
        
        val filter : (elt -> bool) -> t -> t
        
        val partition : (elt -> bool) -> t -> (t, t) prod
        
        val cardinal : t -> nat
        
        val elements : t -> elt list
        
        val choose : t -> elt option
        
        module MF : 
         sig 
          val eqb :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
        
        val min_elt : t -> elt option
        
        val max_elt : t -> elt option
        
        val compare : t -> t -> t compare0
        
        module E : 
         sig 
          type t = TerminalOrderedType.Alt.t
          
          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            TerminalOrderedType.Alt.t compare0
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> sumbool
         end
       end
      
      module StateProdPosMap : 
       sig 
        module E : 
         sig 
          type t = StateProdPosOrderedType.Alt.t
          
          val compare :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            StateProdPosOrderedType.Alt.t compare0
          
          val eq_dec :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            sumbool
         end
        
        module Raw : 
         sig 
          type key = StateProdPosOrderedType.Alt.t
          
          type 'elt tree =
          | Leaf
          | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
          
          val tree_rect :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2
          
          val tree_rec :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2
          
          val height : 'a1 tree -> Z_as_Int.t
          
          val cardinal : 'a1 tree -> nat
          
          val empty : 'a1 tree
          
          val is_empty : 'a1 tree -> bool
          
          val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool
          
          val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option
          
          val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val remove_min :
            'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
            prod
          
          val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
          
          val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree
          
          val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                               t_right : 'elt tree }
          
          val triple_rect :
            ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
          
          val triple_rec :
            ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
          
          val t_left : 'a1 triple -> 'a1 tree
          
          val t_opt : 'a1 triple -> 'a1 option
          
          val t_right : 'a1 triple -> 'a1 tree
          
          val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple
          
          val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
          
          val elements_aux :
            (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
          
          val elements : 'a1 tree -> (key, 'a1) prod list
          
          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
          
          type 'elt enumeration =
          | End
          | More of key * 'elt * 'elt tree * 'elt enumeration
          
          val enumeration_rect :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2
          
          val enumeration_rec :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2
          
          val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
          
          val equal_more :
            ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            ('a1 enumeration -> bool) -> 'a1 enumeration -> bool
          
          val equal_cont :
            ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
            'a1 enumeration -> bool
          
          val equal_end : 'a1 enumeration -> bool
          
          val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
          
          val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
          
          val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
          
          val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
          
          val map2_opt :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3
            tree
          
          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree
            -> 'a3 tree
          
          module Proofs : 
           sig 
            module MX : 
             sig 
              module TO : 
               sig 
                type t = StateProdPosOrderedType.Alt.t
               end
              
              module IsTO : 
               sig 
                
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> sumbool
              
              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> sumbool
              
              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end
            
            module PX : 
             sig 
              module MO : 
               sig 
                module TO : 
                 sig 
                  type t = StateProdPosOrderedType.Alt.t
                 end
                
                module IsTO : 
                 sig 
                  
                 end
                
                module OrderTac : 
                 sig 
                  
                 end
                
                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> sumbool
                
                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> sumbool
                
                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end
             end
            
            module L : 
             sig 
              module MX : 
               sig 
                module TO : 
                 sig 
                  type t = StateProdPosOrderedType.Alt.t
                 end
                
                module IsTO : 
                 sig 
                  
                 end
                
                module OrderTac : 
                 sig 
                  
                 end
                
                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> sumbool
                
                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> sumbool
                
                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end
              
              module PX : 
               sig 
                module MO : 
                 sig 
                  module TO : 
                   sig 
                    type t = StateProdPosOrderedType.Alt.t
                   end
                  
                  module IsTO : 
                   sig 
                    
                   end
                  
                  module OrderTac : 
                   sig 
                    
                   end
                  
                  val eq_dec :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> sumbool
                  
                  val lt_dec :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> sumbool
                  
                  val eqb :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool
                 end
               end
              
              type key = StateProdPosOrderedType.Alt.t
              
              type 'elt t = (StateProdPosOrderedType.Alt.t, 'elt) prod list
              
              val empty : 'a1 t
              
              val is_empty : 'a1 t -> bool
              
              val mem : key -> 'a1 t -> bool
              
              type 'elt coq_R_mem =
              | R_mem_0 of 'elt t
              | R_mem_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list
              | R_mem_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list
              | R_mem_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 
                 bool * 'elt coq_R_mem
              
              val coq_R_mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t
                -> bool -> 'a1 coq_R_mem -> 'a2
              
              val coq_R_mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t
                -> bool -> 'a1 coq_R_mem -> 'a2
              
              val mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
              
              val find : key -> 'a1 t -> 'a1 option
              
              type 'elt coq_R_find =
              | R_find_0 of 'elt t
              | R_find_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
              | R_find_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
              | R_find_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
                 * 'elt option * 'elt coq_R_find
              
              val coq_R_find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
                'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2
              
              val coq_R_find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
                'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2
              
              val find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_find_correct :
                key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
              
              val add : key -> 'a1 -> 'a1 t -> 'a1 t
              
              type 'elt coq_R_add =
              | R_add_0 of 'elt t
              | R_add_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list
              | R_add_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list
              | R_add_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 
                 'elt t * 'elt coq_R_add
              
              val coq_R_add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
                -> 'a1 t -> 'a1 coq_R_add -> 'a2
              
              val coq_R_add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
                -> 'a1 t -> 'a1 coq_R_add -> 'a2
              
              val add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_add_correct :
                key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              
              val remove : key -> 'a1 t -> 'a1 t
              
              type 'elt coq_R_remove =
              | R_remove_0 of 'elt t
              | R_remove_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
              | R_remove_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
              | R_remove_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
                 * 'elt t * 'elt coq_R_remove
              
              val coq_R_remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
                'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
              
              val coq_R_remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
                'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
              
              val remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1
                -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t ->
                'a1 -> (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __
                -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_remove_correct :
                key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
              
              val elements : 'a1 t -> 'a1 t
              
              val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
              
              type ('elt, 'a) coq_R_fold =
              | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
              | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
                 * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 
                 'a * ('elt, 'a) coq_R_fold
              
              val coq_R_fold_rect :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 ->
                'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
              
              val coq_R_fold_rec :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 ->
                'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
              
              val fold_rect :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> 'a2
                -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
              
              val fold_rec :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> 'a2
                -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
              
              val coq_R_fold_correct :
                (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold
              
              val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
              
              type 'elt coq_R_equal =
              | R_equal_0 of 'elt t * 'elt t
              | R_equal_1 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
                 * 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
                 * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list * 
                 bool * 'elt coq_R_equal
              | R_equal_2 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
                 * 'elt * (StateProdPosOrderedType.Alt.t, 'elt) prod list
                 * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t, 'elt) prod list
                 * StateProdPosOrderedType.Alt.t compare0
              | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
              
              val coq_R_equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1
                t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
              
              val coq_R_equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1
                t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
              
              val equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> 'a2
              
              val equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t, 'a1) prod list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> 'a2
              
              val coq_R_equal_correct :
                ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal
              
              val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
              
              val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
              
              val option_cons :
                key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod
                list
              
              val map2_l :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
              
              val map2_r :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
              
              val map2 :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                'a3 t
              
              val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
              
              val fold_right_pair :
                ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 ->
                'a3
              
              val map2_alt :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                (key, 'a3) prod list
              
              val at_least_one :
                'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod
                option
              
              val at_least_one_then_f :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
                option -> 'a3 option
             end
            
            type 'elt coq_R_mem =
            | R_mem_0 of 'elt tree
            | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem
            | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem
            
            val coq_R_mem_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem
              -> 'a2
            
            val coq_R_mem_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem
              -> 'a2
            
            type 'elt coq_R_find =
            | R_find_0 of 'elt tree
            | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find
            | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find
            
            val coq_R_find_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              option -> 'a1 coq_R_find -> 'a2
            
            val coq_R_find_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              option -> 'a1 coq_R_find -> 'a2
            
            type 'elt coq_R_bal =
            | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
            
            val coq_R_bal_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2
            
            val coq_R_bal_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2
            
            type 'elt coq_R_add =
            | R_add_0 of 'elt tree
            | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add
            | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add
            
            val coq_R_add_rect :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
            
            val coq_R_add_rec :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
            
            type 'elt coq_R_remove_min =
            | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
            | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree
               * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
               * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
               * 'elt tree * (key, 'elt) prod
            
            val coq_R_remove_min_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key,
              'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
            
            val coq_R_remove_min_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key,
              'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
            
            type 'elt coq_R_merge =
            | R_merge_0 of 'elt tree * 'elt tree
            | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key, 'elt) prod * 
               key * 'elt
            
            val coq_R_merge_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key
              -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2
            
            val coq_R_merge_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key
              -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2
            
            type 'elt coq_R_remove =
            | R_remove_0 of 'elt tree
            | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
            | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
            
            val coq_R_remove_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              tree -> 'a1 coq_R_remove -> 'a2
            
            val coq_R_remove_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              tree -> 'a1 coq_R_remove -> 'a2
            
            type 'elt coq_R_concat =
            | R_concat_0 of 'elt tree * 'elt tree
            | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key, 'elt) prod
            
            val coq_R_concat_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ ->
              'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
              'a2
            
            val coq_R_concat_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ ->
              'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
              'a2
            
            type 'elt coq_R_split =
            | R_split_0 of 'elt tree
            | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            
            val coq_R_split_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 ->
              'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
              coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
              -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
            
            val coq_R_split_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 ->
              'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
              coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
              -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
            
            type ('elt, 'elt') coq_R_map_option =
            | R_map_option_0 of 'elt tree
            | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt' * 'elt' tree
               * ('elt, 'elt') coq_R_map_option * 'elt' tree
               * ('elt, 'elt') coq_R_map_option
            | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt' tree
               * ('elt, 'elt') coq_R_map_option * 'elt' tree
               * ('elt, 'elt') coq_R_map_option
            
            val coq_R_map_option_rect :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
            
            val coq_R_map_option_rec :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
            
            type ('elt, 'elt', 'elt'') coq_R_map2_opt =
            | R_map2_opt_0 of 'elt tree * 'elt' tree
            | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt'
               * 'elt' tree * Z_as_Int.t * 'elt' tree * 'elt' option
               * 'elt' tree * 'elt'' * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt
            | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt'
               * 'elt' tree * Z_as_Int.t * 'elt' tree * 'elt' option
               * 'elt' tree * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt
            
            val coq_R_map2_opt_rect :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
            
            val coq_R_map2_opt_rec :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
            
            val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
            
            val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
           end
         end
        
        type 'elt bst =
          'elt Raw.tree
          (* singleton inductive, whose constructor was Bst *)
        
        val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
        
        val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
        
        val this : 'a1 bst -> 'a1 Raw.tree
        
        type 'elt t = 'elt bst
        
        type key = StateProdPosOrderedType.Alt.t
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        val remove : key -> 'a1 t -> 'a1 t
        
        val mem : key -> 'a1 t -> bool
        
        val find : key -> 'a1 t -> 'a1 option
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val elements : 'a1 t -> (key, 'a1) prod list
        
        val cardinal : 'a1 t -> nat
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end
      
      val nullable_symb : Aut.Gram.symbol -> bool
      
      val nullable_word : Aut.Gram.symbol list -> bool
      
      val first_nterm_set : Aut.Gram.nonterminal -> TerminalSet.t
      
      val first_symb_set : Aut.Gram.symbol -> TerminalSet.t
      
      val first_word_set : Aut.Gram.symbol list -> TerminalSet.t
      
      val future_of_prod : Aut.Gram.production -> nat -> Aut.Gram.symbol list
      
      val items_map : unit0 -> TerminalSet.t StateProdPosMap.t
      
      val find_items_map :
        TerminalSet.t StateProdPosMap.t -> Aut.state -> Aut.Gram.production
        -> nat -> TerminalSet.t
      
      val forallb_items :
        TerminalSet.t StateProdPosMap.t -> (Aut.state -> Aut.Gram.production
        -> nat -> TerminalSet.t -> bool) -> bool
      
      val is_nullable_stable : unit0 -> bool
      
      val is_first_stable : unit0 -> bool
      
      val is_start_future : TerminalSet.t StateProdPosMap.t -> bool
      
      val is_terminal_shift : TerminalSet.t StateProdPosMap.t -> bool
      
      val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool
      
      val is_non_terminal_goto : TerminalSet.t StateProdPosMap.t -> bool
      
      val is_start_goto : unit0 -> bool
      
      val is_non_terminal_closed : TerminalSet.t StateProdPosMap.t -> bool
      
      val is_complete : unit0 -> bool
     end
    
    type pt_zipper =
    | Top_ptz
    | Cons_ptl_ptz of Aut.Gram.symbol * Aut.GramDefs.token list
       * Aut.Gram.symbol_semantic_type * Aut.Gram.symbol list
       * Aut.GramDefs.token list * tuple * Aut.GramDefs.parse_tree_list
       * ptl_zipper
    and ptl_zipper =
    | Non_terminal_pt_ptlz of Aut.Gram.production * Aut.GramDefs.token list
       * tuple * pt_zipper
    | Cons_ptl_ptlz of Aut.Gram.symbol * Aut.GramDefs.token list
       * Aut.Gram.symbol_semantic_type * Aut.GramDefs.parse_tree
       * Aut.Gram.symbol list * Aut.GramDefs.token list * tuple * ptl_zipper
    
    val pt_zipper_rect :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> 'a1 -> (Aut.Gram.symbol ->
      Aut.GramDefs.token list -> Aut.Gram.symbol_semantic_type ->
      Aut.Gram.symbol list -> Aut.GramDefs.token list -> tuple ->
      Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> Aut.Gram.symbol
      -> Aut.GramDefs.token list -> Aut.Gram.symbol_semantic_type ->
      pt_zipper -> 'a1
    
    val pt_zipper_rec :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> 'a1 -> (Aut.Gram.symbol ->
      Aut.GramDefs.token list -> Aut.Gram.symbol_semantic_type ->
      Aut.Gram.symbol list -> Aut.GramDefs.token list -> tuple ->
      Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> Aut.Gram.symbol
      -> Aut.GramDefs.token list -> Aut.Gram.symbol_semantic_type ->
      pt_zipper -> 'a1
    
    val ptl_zipper_rect :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> (Aut.Gram.production ->
      Aut.GramDefs.token list -> tuple -> pt_zipper -> 'a1) ->
      (Aut.Gram.symbol -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.GramDefs.parse_tree ->
      Aut.Gram.symbol list -> Aut.GramDefs.token list -> tuple -> ptl_zipper
      -> 'a1 -> 'a1) -> Aut.Gram.symbol list -> Aut.GramDefs.token list ->
      tuple -> ptl_zipper -> 'a1
    
    val ptl_zipper_rec :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> (Aut.Gram.production ->
      Aut.GramDefs.token list -> tuple -> pt_zipper -> 'a1) ->
      (Aut.Gram.symbol -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.GramDefs.parse_tree ->
      Aut.Gram.symbol list -> Aut.GramDefs.token list -> tuple -> ptl_zipper
      -> 'a1 -> 'a1) -> Aut.Gram.symbol list -> Aut.GramDefs.token list ->
      tuple -> ptl_zipper -> 'a1
    
    val ptlz_cost :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol list ->
      Aut.GramDefs.token list -> tuple -> ptl_zipper -> nat
    
    val ptz_cost :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol -> Aut.GramDefs.token
      list -> Aut.Gram.symbol_semantic_type -> pt_zipper -> nat
    
    type pt_dot =
    | Reduce_ptd of ptl_zipper
    | Shift_ptd of Aut.Gram.terminal * Aut.Gram.symbol_semantic_type
       * Aut.Gram.symbol list * Aut.GramDefs.token list * tuple
       * Aut.GramDefs.parse_tree_list * ptl_zipper
    
    val pt_dot_rect :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> (ptl_zipper -> 'a1) ->
      (Aut.Gram.terminal -> Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol
      list -> Aut.GramDefs.token list -> tuple ->
      Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1
    
    val pt_dot_rec :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> (ptl_zipper -> 'a1) ->
      (Aut.Gram.terminal -> Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol
      list -> Aut.GramDefs.token list -> tuple ->
      Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1
    
    val ptd_cost :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> pt_dot -> nat
    
    val ptlz_buffer :
      Aut.initstate -> Aut.GramDefs.token list -> Aut.GramDefs.token stream
      -> Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol list ->
      Aut.GramDefs.token list -> tuple -> ptl_zipper -> Aut.GramDefs.token
      stream
    
    val ptz_buffer :
      Aut.initstate -> Aut.GramDefs.token list -> Aut.GramDefs.token stream
      -> Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol ->
      Aut.GramDefs.token list -> Aut.Gram.symbol_semantic_type -> pt_zipper
      -> Aut.GramDefs.token stream
    
    val ptd_buffer :
      Aut.initstate -> Aut.GramDefs.token list -> Aut.GramDefs.token stream
      -> Aut.Gram.symbol_semantic_type -> pt_dot -> Aut.GramDefs.token stream
    
    val ptlz_prod :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol list ->
      Aut.GramDefs.token list -> tuple -> ptl_zipper -> Aut.Gram.production
    
    val ptlz_past :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol list ->
      Aut.GramDefs.token list -> tuple -> ptl_zipper -> Aut.Gram.symbol list
    
    val build_pt_dot :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol list ->
      Aut.GramDefs.token list -> tuple -> Aut.GramDefs.parse_tree_list ->
      ptl_zipper -> pt_dot
    
    val pop_ptlz :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.Gram.symbol list ->
      Aut.GramDefs.token list -> tuple -> Aut.GramDefs.parse_tree_list ->
      ptl_zipper -> (Aut.GramDefs.token list, (Aut.Gram.symbol_semantic_type,
      (pt_zipper, Aut.GramDefs.parse_tree) prod) sigT) sigT
    
    val next_ptd :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> pt_dot -> pt_dot option
    
    val init_ptd :
      Aut.initstate -> Aut.GramDefs.token list ->
      Aut.Gram.symbol_semantic_type -> Aut.GramDefs.parse_tree -> pt_dot
   end
  
  val complete_validator : unit0 -> bool
  
  val safe_validator : unit0 -> bool
  
  val parse :
    Aut.initstate -> nat -> Aut.GramDefs.token stream -> Inter.parse_result
 end

