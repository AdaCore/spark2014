procedure Test_Exceptional with SPARK_Mode is
   --  A by-copy formal is not preserved on exceptional return

   procedure By_Copy (X : in out Integer; Can_Modify : Boolean) with
     Pre => X = 0,
     Modifies => (X when Can_Modify),
     Exceptional_Cases => (Program_Error => True),
     No_Return;

   procedure By_Copy (X : in out Integer; Can_Modify : Boolean) is
   begin
      X := 1;
      raise Program_Error;
   end By_Copy;

   type Pair is record
      F, G : Integer;
   end record;

   procedure Partial_By_Copy (X : in out Pair) with
     Pre => X.G = 0,
     Modifies => X.F,
     Exceptional_Cases => (Program_Error => True),
     No_Return;

   procedure Partial_By_Copy (X : in out Pair) is
   begin
      X.G := 1;
      raise Program_Error;
   end Partial_By_Copy;

   --  By-reference formals still need to be preserved

   procedure By_Reference (X : aliased in out Integer; Can_Modify : Boolean) with
     Pre => X = 0,
     Modifies => (X when Can_Modify), --  @MODIFIES:FAIL
     Exceptional_Cases => (Program_Error => True),
     No_Return;

   procedure By_Reference (X : aliased in out Integer; Can_Modify : Boolean) is
   begin
      X := 1;
      raise Program_Error;
   end By_Reference;

   --  A captured formal is a global of the nested procedure

   procedure Outer (X : in out Integer) with Pre => X = 0 is
      procedure Inner (Can_Modify : Boolean) with
        Modifies => (X when Can_Modify), --  @MODIFIES:FAIL
        Exceptional_Cases => (Program_Error => True),
        No_Return;

      procedure Inner (Can_Modify : Boolean) is
      begin
         X := 1;
         raise Program_Error;
      end Inner;
   begin
      null;
   end Outer;

   --  By-copy formals still need to be preserved on normal return

   procedure Normal_Return (X : in out Integer; Can_Modify : Boolean) with
     Pre => X = 0,
     Modifies => (X when Can_Modify) --  @MODIFIES:FAIL
   is
   begin
      X := 1;
   end Normal_Return;

   --  Component checks also apply to captured formals on exceptional exit

   type Variant_Record (D : Boolean := False) is record
      case D is
         when True =>
            F : Integer;
         when False =>
            null;
      end case;
   end record;

   procedure Outer_Component (X : in out Variant_Record) is
      procedure Inner with
        Pre => X.D and not X'Constrained,
        Modifies => X.F, --  @DISCRIMINANT_CHECK:FAIL @MODIFIES:FAIL
        Exceptional_Cases => (Program_Error => True),
        No_Return;

      procedure Inner is
      begin
         X := (D => False);
         raise Program_Error;
      end Inner;
   begin
      null;
   end Outer_Component;
begin
   null;
end Test_Exceptional;
