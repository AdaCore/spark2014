package UU2 is

   type T (Flag : Boolean := False) is
   record
       case Flag is
           when False =>
               F1 : Float := 0.0;
           when True =>
               F2 : Integer := 0;
       end case;
    end record
    with Unchecked_Union;

   function Eq (X, Y : T) return Boolean is (X = Y);

   type R is record
      C : T;
   end record;

   function Eq (X, Y : R) return Boolean is (X = Y);

   subtype TF is T(False);

   function Mem (X : T) return Boolean is (X in TF);

   type T2 (Flag : Boolean := False) is
   record
       case Flag is
           when False =>
               F1 : Float := 0.0;
           when True =>
               F2 : Integer := 0;
       end case;
   end record;

   type T2D is new T2
     with Unchecked_Union;

   function Conv (X : T2D) return T2 is (T2(X));

end UU2;
