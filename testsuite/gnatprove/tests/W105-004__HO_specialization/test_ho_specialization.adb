procedure Test_HO_Specialization (B : Boolean)
  with
    SPARK_Mode => On
is

   --  Functions with one or more specializable parameters

   function Call (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Depends => (Call'Result => F),
     Post => Call'Result = F.all;

   function Call (F : not null access function return Integer) return Integer is
   begin
      return F.all;
   end Call;

   function Call_2 (F, G : not null access function return Integer; B : Boolean) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Depends => (Call_2'Result => (F, G, B)),
     Post => (if B then Call_2'Result = F.all else Call_2'Result = G.all);

   function Call_2 (F, G : not null access function return Integer; B : Boolean) return Integer is
   begin
      if B then
         return F.all;
      else
         return G.all;
      end if;
   end Call_2;

   --  Function which uses F in a way which is not compatible with specialization
   function Non_Specialized_Read (F : access function return Integer) return Boolean is (F /= null);

   --  Uses that cannot be specialized are OK in refined post which is never specialized
   package Nested is
      function Use_In_Refined_Post (F : not null access function return Integer) return Integer with
        Annotate => (GNATprove, Higher_Order_Specialization),
        Post => Use_In_Refined_Post'Result = F.all;
   end;

   package body Nested is
      function Use_In_Refined_Post (F : not null access function return Integer) return Integer is
        (F.all)
        with
          Refined_Post => Non_Specialized_Read (F) and then Use_In_Refined_Post'Result = F.all;
   end;

   --  Uses that cannot be specialized are OK in expression function body which is never specialized

   function Use_In_Expr (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Use_In_Expr'Result = F.all;

   function Use_In_Expr (F : not null access function return Integer) return Integer is
     (if Non_Specialized_Read (F) then F.all else 0);

   V : Integer := 0;

   function Read_V return Integer is (V) with Pre => V >= 0;
   function Read_V_2 return Integer is (V) with Pre => V < 0;
   function Cst_1 return Integer is (1);
   function Cst_2 return Integer is (2);

   H : not null access function return Integer := Cst_2'Access;
   I : Integer;
begin
   --  Calls (specialized or not) of functions with specializable parameters

   I := Call (H);
   pragma Assert (I = 2);
   I := Call (Cst_1'Access);
   pragma Assert (I = 1);
   I := Call (Read_V'Access);
   pragma Assert (I = 0);
   I := Call_2 (Read_V'Access, Cst_1'Access, B);
   pragma Assert (I = (if B then 0 else 1));
   I := Call_2 (H, Cst_1'Access, B);
   pragma Assert (I = (if B then 2 else 1));
   I := Call_2 (Read_V'Access, H, B);
   pragma Assert (I = (if B then 0 else 2));
   I := Call_2 (H, H, B);
   pragma Assert (I = 2);
   I := Call (Read_V_2'Access); -- @WEAKER_PRE_ACCESS:FAIL
end Test_HO_Specialization;
