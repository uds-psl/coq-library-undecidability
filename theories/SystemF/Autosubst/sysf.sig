-- Signature for System F

-- the types
pureterm : Type
polytype : Type
term : Type

-- the constructors for pureterm
pureapp  : pureterm -> pureterm -> pureterm
pureabs  : (pureterm -> pureterm) -> pureterm

-- the constructors for polytype
polyarr : polytype -> polytype -> polytype
polyabs : (polytype -> polytype) -> polytype

-- the constructors for term
app    : term -> term -> term
abs    : polytype -> (term -> term) -> term
tyapp : term -> polytype -> term
tyabs : (polytype -> term) -> term
