package Hidden_Private_Part with
   SPARK_Mode
is
   function Id (X : Integer) return Integer is (X);

   type T is private;

   function Return_0 return Integer;

   function Return_1 return Integer is (1);

   function Return_2 return Integer;

   function Return_2 return Integer is (2);

   Zero : constant Integer;

   One : constant Integer := Id (1);

   type T_P1 (D : Integer := 1) is private with
     Default_Initial_Condition => D /= 0,
     Predicate => D /= 0;

   type T_P2 (D : Integer := 1) is private with
     Default_Initial_Condition => D /= 0;

private
   pragma Annotate (GNATprove, Hide_Info, "Private_Part");

   type R is record
      F     : Integer;
      Dummy : Boolean;
   end record;

   function "=" (X, Y : R) return Boolean is (X.F = Y.F);

   type T is record
      G : R;
   end record;

   function Return_0 return Integer is (0);

   Zero : constant Integer := Id (0);

   function F_Hidden return Boolean is (True);

   type T_P1 (D : Integer := 1) is null record;

   type T_P2 (D : Integer := 1) is null record with
     Predicate => D /= 0;

   --  Non-conforming types which are not visible from the public part
   --  of the package are OK.

   type Int_Acc is access all Integer;

   type Int_Relaxed is new Integer with Relaxed_Initialization;

   type Only_Relaxed is record
      F1, F2 : Int_Relaxed;
   end record;
end Hidden_Private_Part;
