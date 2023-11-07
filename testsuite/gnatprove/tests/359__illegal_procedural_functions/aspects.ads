package Aspects is

   function F1 return Boolean with
     Annotate => (GNATprove, Inline_For_Proof),
     Post => F1'Result = True,
     Side_Effects;

   function F2 return Boolean with
     Annotate => (GNATprove, Inline_For_Proof),
     Post => F2'Result = True,
     Volatile_Function;

   type T is tagged null record;
   function F3 (X : T) return Boolean with
     Annotate => (GNATprove, Inline_For_Proof),
     Post => F3'Result = True;

   function F4 (X : access Integer) return access Integer with
     Annotate => (GNATprove, Inline_For_Proof),
     Post => F4'Result = null;

end Aspects;
