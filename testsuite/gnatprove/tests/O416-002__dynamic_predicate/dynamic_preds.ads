package Dynamic_Preds
  with SPARK_Mode
is
   subtype Even is Integer with Dynamic_Predicate => Even mod 2 = 0;

   type Even_Pair is record
      A : Even;
      B : Even;
   end record;

   type Ext_Even_Pair is record
      A : Integer;
      B : Integer;
   end record with Dynamic_Predicate => Ext_Even_Pair.A in Even and Ext_Even_Pair.B in Even;

   procedure Init_Even (X : in out Integer);
   procedure Init_OK_Even (X : in out Integer)
     with Post => X in Even;
   procedure Call_Init_Even (X : in out Even);
   procedure Call2_Init_Even (X : in out Integer)
     with Pre => X mod 2 = 0;
   procedure Call3_Init_Even (X : in out Even_Pair);
   procedure Call4_Init_Even (X : in out Ext_Even_Pair);

   subtype Even_Close_Pair is Even_Pair
     with Dynamic_Predicate => Even_Close_Pair.B = Even_Close_Pair.A + 2;

   procedure Init_Even_Pair (X : out Even_Pair; A, B : Integer);
   procedure Init_Constant_Even_Pair (X : out Even_Pair);
   procedure Init_Even_Close_Pair (X : out Even_Close_Pair);

   function Get_Even_Pair (A, B : Integer) return Even_Pair
     with Pre => A in Even;
   function Get_OK_Even_Pair (A, B : Even) return Even_Pair;
   function Get_Constant_Even_Pair return Even_Pair
     with Post => Get_Constant_Even_Pair'Result.A = 0
                    and then
                  Get_Constant_Even_Pair'Result.B = 0;
   function Get_Even_Close_Pair (Above : Integer) return Even_Close_Pair;
   function Get_Even_Close_Pair_Error (Above : Integer) return Even_Close_Pair;
   function Get_Even_Close_Pair_Wrong (Above : Integer) return Even_Close_Pair;

   procedure Update_Even_Pair (X : in out Even_Pair; A, B : Integer);
   procedure Update_Constant_Even_Pair (X : in out Even_Pair)
     with Post => X.A = 0 and X.B = 2;
   procedure Update_Even_Close_Pair (X : in out Even_Close_Pair);
   function Get_Even_Close_Pair (X : Even_Close_Pair) return Even_Close_Pair;
   procedure Update_Bad_Even_Pair (X : in out Even_Pair);
   procedure Update_Bad2_Even_Pair (X : in out Even_Pair);

end Dynamic_Preds;
