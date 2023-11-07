procedure Test_Relaxed_Borrower with SPARK_Mode is

   --  Test relaxed init on local borrowers in simple borrows

   type Holder is record
      Content : Integer;
   end record;

   type H_Acc is not null access Holder;

   type List;
   type List_Access is access List;
   type List is record
      Value : H_Acc;
      Next  : List_Access;
   end record;

   procedure Update_Init (X : out Holder) with
     Relaxed_Initialization => X,
     Post => X'Initialized;

   procedure Update_Init (X : out Holder) is
   begin
      X := (Content => 1);
   end Update_Init;

   procedure Update_Uninit (X : out Holder) with
     Relaxed_Initialization => X;

   procedure Update_Uninit (X : out Holder) is
      U : Holder with Relaxed_Initialization;
   begin
      X := U;
   end Update_Uninit;

   procedure Update_Last_OK (L : in out List_Access) with
     Pre => L /= null;

   procedure Update_Last_OK (L : in out List_Access) is
      X : not null access List := L;
   begin
      while X.Next /= null loop
         X := X.Next;
      end loop;
      declare
         V : not null access Holder := X.Value with Relaxed_Initialization; -- @INIT_BY_PROOF:PASS
      begin
         Update_Init (V.all);
      end;
   end Update_Last_OK;

   procedure Update_Last_Bad (L : in out List_Access) with
     Pre => L /= null;

   procedure Update_Last_Bad (L : in out List_Access) is
      X : not null access List := L;
   begin
      while X.Next /= null loop
         X := X.Next;
      end loop;
      declare
         V : not null access Holder := X.Value with Relaxed_Initialization; -- @INIT_BY_PROOF:FAIL
      begin
         Update_Uninit (V.all);
      end;
   end Update_Last_Bad;


begin
   null;
end Test_Relaxed_Borrower;
