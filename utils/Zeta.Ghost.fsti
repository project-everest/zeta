module Zeta.Ghost

val hoist_ghost (#a:Type) (#b:a -> Type) (f:(x:a -> GTot (b x)))
  : GTot (x:a -> b x)

val hoist_ghost_apply (#a:Type) (#b:a -> Type) (f:(x:a -> GTot (b x))) (x:a)
  : Lemma ((hoist_ghost f) x == f x)
          [SMTPat ((hoist_ghost f) x)]

val hoist_ghost2 (#a:Type) (#b:a -> Type) (#c:(x:a -> b x -> Type))
  (f:(x:a -> y:b x -> GTot (c x y)))
  : GTot (x:a -> y:b x -> c x y)

val hoist_ghost2_apply (#a:Type) (#b:a -> Type) (#c:(x:a -> b x -> Type)) (f:(x:a -> y:b x -> GTot (c x y)))
  (x:a) (y:b x)
  : Lemma ((hoist_ghost2 f) x y == f x y)
          [SMTPat ((hoist_ghost2 f) x y)]

open FStar.FunctionalExtensionality

val hoist_ghost_restricted (#a:Type) (#b:a -> Type) (f:restricted_g_t a b)
  : GTot (g:restricted_t a b{forall x. f x == g x})

val hoist_ghost_restricted_apply (#a:Type) (#b:a -> Type) (f:restricted_g_t a b) (x:a)
  : Lemma ((hoist_ghost_restricted f) x == f x)
          [SMTPat ((hoist_ghost_restricted f) x)]
