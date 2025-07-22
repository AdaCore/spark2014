procedure Illegal
  with
    SPARK_Mode => On
is
   --  Higher_Order_Specialization with no entities
   pragma Annotate (GNATprove, Higher_Order_Specialization, "toto");

   --  Higher_Order_Specialization applied to a type
   type T is new Integer with
     Annotate => (GNATprove, Higher_Order_Specialization);

   --  Higher_Order_Specialization applied to non ghost procedure

   procedure Non_Ghost_Proc (F : not null access function return Integer) with
     Annotate => (GNATprove, Higher_Order_Specialization);

   procedure Non_Ghost_Proc (F : not null access function return Integer) is null;

   --  Higher_Order_Specialization applied to procedure with out params

   procedure Proc_Out_Param (I : out Integer; F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization);

   procedure Proc_Out_Param (I : out Integer; F : not null access function return Integer) is
   begin
      I := F.all;
   end Proc_Out_Param;

   --  Higher_Order_Specialization applied to procedure with a global out

   Global_V : Integer;

   procedure Proc_Out_Global (F : not null access function return Integer) with
     Ghost,
     Global => (Output => Global_V),
     Annotate => (GNATprove, Higher_Order_Specialization);

   procedure Proc_Out_Global (F : not null access function return Integer) is
   begin
      Global_V := F.all;
   end Proc_Out_Global;

   --  Higher_Order_Specialization applied to a volatile function
   function Volatile_Fun (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Volatile_Function;

   function Volatile_Fun (F : not null access function return Integer) return Integer is (F.all);

   package Nested is
      type Root is tagged null record;

      --  Higher_Order_Specialization applied to a dispatching function
      function Dispatch_Fun (R : Root; F : not null access function return Integer) return Integer with
        Annotate => (GNATprove, Higher_Order_Specialization);

      function Dispatch_Fun (R : Root; F : not null access function return Integer) return Integer is (F.all);
   end Nested;

   type My_Arr is array (Character) of aliased Integer;

   --  Higher_Order_Specialization applied to a borrowing traversal function
   function Borrowing_Fun (X : not null access My_Arr; F : not null access function return Character) return access Integer with
     Annotate => (GNATprove, Higher_Order_Specialization);

   function Borrowing_Fun (X : not null access My_Arr; F : not null access function return Character) return access Integer is
     (X (F.all)'Access);

   --  Higher_Order_Specialization applied to function with no specializable
   --  parameters.
   function No_Fun_Params (I : Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization);

   function No_Fun_Params (I : Integer) return Integer is (I);

   --  Function which uses F in a way which is not compatible with specialization
   function Non_Specialized_Read (F : access function return Integer) return Boolean is (F /= null);

   --  Non specializable use of formal in precondition
   function Use_In_Pre (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre => Non_Specialized_Read (F);

   function Use_In_Pre (F : not null access function return Integer) return Integer is (F.all);

   --  Non specializable use of formal in postcondition
   function Use_In_Post (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Non_Specialized_Read (F);

   function Use_In_Post (F : not null access function return Integer) return Integer is (F.all);

   --  Non specializable use of formal in guards of a contract cases
   function Use_In_CC1 (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Contract_Cases =>
       (Non_Specialized_Read (F) =>
          Use_In_CC1'Result = F.all,
        others                   =>
          True);

   function Use_In_CC1 (F : not null access function return Integer) return Integer is (F.all);

   function Use_In_CC1_bis (F : access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Contract_Cases =>
       (F /= null =>
          Use_In_CC1_bis'Result = F.all,
        others                   =>
          True);

   function Use_In_CC1_bis (F : access function return Integer) return Integer is (F.all);

   --  Non specializable use of formal in posts of a contract cases
   function Use_In_CC2 (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Contract_Cases =>
       (F.all > 0 =>
          Non_Specialized_Read (F),
        others    =>
          True);

   function Use_In_CC2 (F : not null access function return Integer) return Integer is (F.all);

   --  Non specializable use of formal in variants
   function Use_In_Variants (F : not null access function return Integer; C : Natural) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Subprogram_Variant => (Decreases => Non_Specialized_Read (F), Decreases => C);

   function Use_In_Variants (F : not null access function return Integer; C : Natural) return Integer is
     (if C = 0 then 0 else Use_In_Variants (F, C - 1));

   --  Comparison to null is not supported yet

   function Eq_In_Pre (F : access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Pre => F /= null;

   function Eq_In_Pre (F : access function return Integer) return Integer is
   begin
      return F.all;
   end Eq_In_Pre;

   --  Annotations with Exceptional_Cases and Always_Terminates

   procedure Exc_Ok (F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Exceptional_Cases =>
       (others => False);

   procedure Exc_Ok (F : not null access function return Integer) is
   begin
     null;
   end Exc_Ok;

   procedure Term_Ok (F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Always_Terminates => True;

   procedure Term_Ok (F : not null access function return Integer) is
   begin
     null;
   end Term_Ok;

   procedure Exc_Bad (F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Exceptional_Cases =>
       (others => True);

   procedure Exc_Bad (F : not null access function return Integer) is
   begin
     null;
   end Exc_Bad;

   procedure Term_Bad (F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Always_Terminates => False;

   procedure Term_Bad (F : not null access function return Integer) is
   begin
     null;
   end Term_Bad;
begin
   null;
end Illegal;
