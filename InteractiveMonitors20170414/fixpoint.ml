(*                   All the different ways to get 
 *            the _fully polymorphic_ fixpoint in OCaml 
 *
 * This code has been inspired and influenced by Omega implementations
 *   http://www.lri.fr/~signoles/prog/misc/lambda.ml.html
 *   by Julien SIGNOLES.
 * 
 * This code fixes one bug in SIGNOLES' code, and develops
 * the fixpoint operator with full polymorphism. Our approach is 
 * based explicitly on self-application.
 * We also add more implementations: recursive modules, and the 
 * fixpoint inherent in objects.
 *
 * $Id: fixpoints.ml,v 1.3 2005/11/22 06:26:05 oleg Exp oleg $
 *)

(* The desired signature we are implementing (in quite a few ways) here
*)
module type FIX = sig
  val fix : (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)
end

(* A simple test of FIX *)
module Fact(F : FIX) = struct
  let fact_nr self n = if n = 0 then 1 else n * (self (n-1))
  let fact n = F.fix fact_nr n
  let fact5 = fact 5
end

(*------------------------------------------------------------------------*)

(* The native implementation, via built-in let rec *)
module FixNative : FIX = struct
  let rec fix f n = f (fix f) n
end

let test = let module F = Fact(FixNative) in F.fact5
;;

(* The following is essentially the same, but cuter *)
module FixModule : FIX = struct
  module rec M : FIX = struct
    let fix f n = f (M.fix f) n
  end
  include M
end

let test = let module F = Fact(FixModule) in F.fact5
;;

(*------------------------------------------------------------------------*)

(* Implementing Fix via iso-recursive types 
 *
 * The standard formula for the applicative fixpoint combinator
 *    fix f === (fun g -> g g)(fun x n -> f (x x) n)
 * obviously does not type.
 * Indeed, the type of 'g' must be both t->a->b and t, i.e., must be
 * recursive. We can emulate this (equi-) recursive type with an 
 * iso-recursive one.
*)

(* Iso-recursive algebraic data type. 
 * Following SIGNOLES, we rely on an iso-recursive datatype ('a,'b) t
 * with the injection function Wrap :   (('a,'b) t -> ('a->'b)) -> ('a,'b) t
 * and  the projection function unwrap: ('a,'b) t -> (('a,'b) t -> ('a->'b))
 *)
module FixData : FIX = struct
  type ('a,'b) t = Wrap of (('a,'b) t -> ('a->'b))
  let unwrap (Wrap x) = x
  let fix f = ((fun g -> g (Wrap g)) (fun x n -> f (unwrap x x) n))
end

let test = let module F = Fact(FixData) in F.fact5
;;


(* A different take. Instead of wrapping/unwrapping, we attempt to
 * define a function auto'apply such that 
 *  auto'apply g applies g to itself, in some way that makes the
 * typechecker happy.
 * The following implementation uses the recursive datatype, the same
 * as above.
 *)
module FixData2 : FIX = struct
  type ('a,'b) t = Wrap of (('a,'b) t -> ('a->'b))
  let auto'apply ((Wrap x) as g) = x g
  let fix f = auto'apply (Wrap (fun x n -> f (auto'apply x) n))
end

let test = let module F = Fact(FixData2) in F.fact5
;;


(* essentially the same as above *)
module FixRecord : FIX = struct
  type ('a,'b) t = { unwrap : ('a,'b) t -> ('a->'b) }
  let auto'apply g = g.unwrap g
  let fix f = auto'apply {unwrap = (fun x n -> f (auto'apply x) n)}
end

let test = let module F = Fact(FixRecord) in F.fact5
;;

(* Also essentially the same as above: an object is a kind of record.
   See however below for FixObjectS: objects have an implicit
   fixpoint already.
*)
module FixObjectR : FIX = struct
  class ['a,'b] t y = 
    object method unwrap (x: ('a,'b) t) (n:'a) : 'b = y x n end
  let auto'apply g = g#unwrap g
  let fix f = auto'apply (new t (fun x n -> f (auto'apply x) n))
end

let test = let module F = Fact(FixObjectR) in F.fact5
;;

(* essentially the same as above. Polymorphic variants don't
   need an explicit type declaration.
   They still can have (iso-) recursive type 
*)
module FixPVar : FIX = struct
  let auto'apply ((`Unwrap f) as g) = f g
  let fix f = auto'apply (`Unwrap (fun x n -> f (auto'apply x) n))
end

let test = let module F = Fact(FixPVar) in F.fact5
;;

(* Here the value to auto'apply is implicit -- passed via an environment
   (continuation) rather than given as an explicit argument to auto'apply.
   Delimited continuations do have recursive types.
   See FixReference for the canonical form of using references for
   implementing fixpoints.
 *)
module FixReferenceA : FIX = struct
  let fix f = 
    let wrap = ref (fun _ -> failwith "undefined") in
    let auto'apply () = !wrap in
    auto'apply (wrap := (fun n -> f (auto'apply ()) n))
end

let test = let module F = Fact(FixReferenceA) in F.fact5
;;

(*------------------------------------------------------------------------*)
(* Equi-recursive types *)

module FixMagic: FIX = struct
  let auto'apply g = Obj.magic g g
  let fix f = auto'apply (fun x n -> f (auto'apply x) n)
end

let test = let module F = Fact(FixMagic) in F.fact5
;;

(* True equi-recursive types. Need -rectypes flag to the Ocaml *)
(*
module FixERec: FIX = struct
  let auto'apply g = g g
  let fix f = auto'apply (fun x n -> f (auto'apply x) n)
end

let test = let module F = Fact(FixERec) in F.fact5
;;
*)


(*------------------------------------------------------------------------*)

(* Mutation: mutation is implicitly a delimited continuation, which
   has a recursive type
*)

module FixReference : FIX = struct
  let fix f n = 
    let cell = ref (fun _ -> failwith "undefined") in
    begin cell := f (fun n -> !cell n); !cell n end
end

let test = let module F = Fact(FixReference) in F.fact5
;;

(* Exceptions are also continuations with recursive types.
   We needed to declare the record rfe below to get the polymorphism
   right.
*)
module FixException : FIX = struct
  type rfe = {lu : 'a 'b . (('a -> 'b) -> ('a -> 'b)) -> 
                            ((unit -> 'b) -> 'a -> 'b)}
  exception FE of rfe
  let u f g = f (fun n -> try g () with FE {lu = u'} -> u' f g n)
  let fix f = u f (fun () -> raise (FE {lu = u}))
end


let test = let module F = Fact(FixException) in F.fact5
;;

(* Objects already have fixpoints in them *)
module FixObjectS : FIX = struct
  class fixc = 
    object (self) 
      method fix' : 'a 'b. (('a->'b)->('a ->'b)) -> ('a->'b) = 
	fun f n -> f (self#fix' f) n end
  let fix f = (new fixc)#fix' f
end

let test = let module F = Fact(FixObjectS) in F.fact5
;;
