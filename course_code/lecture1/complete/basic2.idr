module Basic2

vApp : Vect (a -> b) n -> Vect a n -> Vect b n
vApp []       []         = []
vApp (f :: fs) (a :: as) = f a :: vApp fs as
