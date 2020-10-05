From mathcomp Require Import all_ssreflect all_algebra.
From categories Require Import classical category functor natural.
From mathcomp.analysis Require Import topology.

Open Scope category_scope.
Open Scope classical_set_scope.

Declare Scope sheaf_scope.
Delimit Scope sheaf_scope with sheaf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Module OpenSet.
  Definition mixin_of (T : topologicalType) (U : set T) := open U.
  Notation class_of := mixin_of.
  
  Section ClassDef.
    Structure type (T : topologicalType) := Pack { U : set T ; _ : class_of U }.
    Local Coercion U : type >-> set.

    Variables (T : topologicalType) (U : set T) (cU : type T).
    Definition class := let: Pack _ c as cU' := cU return class_of cU' in c.
  End ClassDef.
  Arguments Pack {T} {U} _.
  
  Module Exports.
    Notation openType := type.
    Coercion U : type >-> set.
    Notation IsOpen := mixin_of.
    Notation Open fU := (Pack fU).
  End Exports.
End OpenSet.
Import OpenSet.Exports.

Section opens.
  Variable (T : topologicalType).
  Variable (U V : openType T).
  
  Definition openT0 : openType T := Open open0.
  Definition openTT : openType T := Open openT.
End opens.

Section opens_category.
  Variable T : topologicalType.
  
  Definition opens_mixin := @CatMixin
                              (@openType T) subset
                              (fun U V W subUV subVW => subset_trans subUV subVW)
                              (fun U V W Y subUV subVW subWY => @Prop_irrelevance _ _ _)
                              (fun X _ => ssrfun.id)
                              (fun _ _ _ => @Prop_irrelevance _ _ _)
                              (fun _ _ _ => @Prop_irrelevance _ _ _).

  Definition opens_Category := Eval hnf in Category (@openType T) opens_mixin.
  Canonical opens_Category.
End opens_category.
Notation opens T := (opens_Category T).

(* A presheaf is just a covariant functor from opens(X) to a category C *)
Notation presheaf X C := (functor ((opens X)^op) C).

(* The category of presheaves, so that we get morphisms of functors for free *)
Notation PSh X C := ([((opens X)^op) ; C]).

Section presheaf.
  Variables (X : topologicalType) (V U: opens X) (C : category).
  Variable (F : PSh X C).  
  Hypothesis UV_incl : U `<=` V.

  Definition res := F @@ UV_incl.
End presheaf.
Arguments res {X} V U {C} {F}.

Section sheaf_axiom.
  Variables (X : topologicalType) (U : openType X) (C : category).
  Variables (I : choiceType) (D : set I) (b : I -> set X).
  Hypothesis b_cover : \bigcup_(i in D) b i = U.

  Variable F : presheaf X C.
End sheaf_axiom.
