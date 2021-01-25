package UU
  with SPARK_Mode => On
is
   type R (F : Boolean := True) is record
      case F is
         when False =>
            FI : Integer;
         when True =>
            FF : Float;
      end case;
   end record
     with Unchecked_Union;

   type Holder is record
      C : R;
   end record;

   subtype FR is R (True);

   function C (Left, Right : in R) return Boolean;

   function C2 (Left, Right : in FR) return Boolean;

   function C3 (Left : in FR;
                Right : in R) return Boolean;

   function C4 (Left, Right : in Holder) return Boolean;

   type Root1 is tagged record
      C : R;
   end record;

   function C5 (Left, Right : in Root1'Class) return Boolean;

   type Root2 is tagged record
      I : Integer;
   end record;

   type Child2 is new Root2 with record
      C : FR;
   end record;

   function C6 (Left, Right : in Root2'Class) return Boolean;

   type R2 (F : Boolean := True) is record
      G : Integer;
      case F is
         when False =>
            FI : Integer;
         when True =>
            FF : Float;
      end case;
   end record
     with Unchecked_Union;

   function "=" (X, Y : R2) return Boolean is (X.G = Y.G);

   type Holder2 is record
      C : R2;
   end record;

   type Holder3 is tagged record
      C : R2;
   end record;

   type Child_Holder3 is new Holder3 with record
      D : R;
   end record;

   type Holder4 is record
      C : FR;
   end record;

   type Holder5 is record
      C : R (True);
   end record;

   function C7 (Left, Right : in Holder2) return Boolean;

   function C8 (Left, Right : in Holder3'Class) return Boolean;

   function C9 (Left, Right : in Holder4) return Boolean;

   function C10 (Left, Right : in Holder5) return Boolean;

end UU;
