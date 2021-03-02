nat : Type
term : Type

const : nat -> term
app : term -> term -> term
lam : term -> (term -> term) -> term
Pi : term -> (term -> term) -> term