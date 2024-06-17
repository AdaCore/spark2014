package Logical_Equality_Implementation with SPARK_Mode is

   --  Scalar types

   type My_Bool is new Boolean;
   function Eq (X, Y : My_Bool) return Boolean is
     (X = Y)
   with Annotate => (GNATprove, Logical_Equal);

   type My_Int is range 1 .. 100;
   function Eq (X, Y : My_Int) return Boolean is
     (X = Y)
   with Annotate => (GNATprove, Logical_Equal);

   type My_Mod is mod 42;
   function Eq (X, Y : My_Mod) return Boolean is
     (X = Y)
   with Annotate => (GNATprove, Logical_Equal);

   type My_Float is digits 4;
   function Eq (X, Y : My_Float) return Boolean is
     (X = Y and then My_Float'Copy_Sign (1.0, X) = My_Float'Copy_Sign (1.0, Y))
   with Annotate => (GNATprove, Logical_Equal);

   --  Composite types

   type Constr_Arr is array (Positive range 1 .. 100) of My_Float;
   function Eq (X, Y : Constr_Arr) return Boolean is
     (for all I in 1 .. 100 => Eq (X (I), Y (I)))
   with Annotate => (GNATprove, Logical_Equal);

   type Unconstr_Arr is array (Positive range <>) of My_Int;
   function Eq (X, Y : Unconstr_Arr) return Boolean is
     (X = Y and then X'First = Y'First and then X'Last = Y'Last)
   with Annotate => (GNATprove, Logical_Equal);

   type My_Rec (D : My_Bool) is record
      case D is
	 when True =>
           F : My_Int;
           G : My_Mod;
	 when False =>
           H : My_Float;
           A : Constr_Arr;
      end case;
   end record;
   function Eq (X, Y : My_Rec) return Boolean is
     (Eq (X.D, Y.D) and then
       (if X.D then Eq (X.F, Y.F) and then Eq (X.G, Y.G)
        else Eq (X.H, Y.H) and then Eq (X.A, Y.A)))
   with Annotate => (GNATprove, Logical_Equal);

end Logical_Equality_Implementation;
