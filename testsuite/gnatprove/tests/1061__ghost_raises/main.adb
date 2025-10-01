pragma Assertion_Level (L1);
pragma Assertion_Level (L2, Depends => [L1]);
pragma Assertion_Level (L3);

procedure Main with SPARK_Mode is
   pragma Assertion_Policy (Ghost => Ignore);

   procedure Raise_PE (B : Boolean)
   with
     Ghost             => Static,
     Exceptional_Cases => (Program_Error => B),
     Post              => not B
   is
   begin
      if B then
         raise Program_Error;
      end if;
   end Raise_PE;

   procedure Catch_PE (B : Boolean) with Ghost => Runtime, Post => True is
   begin
      Raise_PE (B); --  @RAISE:FAIL exception propagated from ignored ghost context to checked ghost context
      pragma Assert (Runtime => not B);
   exception
      when Program_Error =>
         null;
   end Catch_PE;

   procedure Raise_PE_2 (B : Boolean)
   with Ghost => L2, Exceptional_Cases => (Program_Error => B), Post => not B
   is
   begin
      if B then
         raise Program_Error;
      end if;
   end Raise_PE_2;

   procedure Catch_PE_2 (B : Boolean) with Ghost => L1, Post => True is
   begin
      Raise_PE_2 (B); -- @RAISE:FAIL exception propagated from incompatible ghost levels
      pragma Assert (Runtime => not B);
   exception
      when Program_Error =>
         null;
   end Catch_PE_2;

   procedure Raise_PE_2_bis (B : Boolean)
   with Ghost => L3, Exceptional_Cases => (Program_Error => B), Post => not B
   is
   begin
      if B then
         raise Program_Error;
      end if;
   end Raise_PE_2_bis;

   procedure Catch_PE_2_bis (B : Boolean) with Ghost => L1, Post => True is
   begin
      Raise_PE_2_bis (B); -- @RAISE:FAIL exception propagated from incompatible ghost levels
      pragma Assert (Runtime => not B);
   exception
      when Program_Error =>
         null;
   end Catch_PE_2_bis;

   procedure Raise_PE_3 (B : Boolean)
   with Ghost, Exceptional_Cases => (Program_Error => B), Post => not B
   is
   begin
      if B then
         raise Program_Error;
      end if;
   end Raise_PE_3;

   procedure Catch_PE_3 (B : Boolean) with Ghost => Runtime, Post => True is
   begin
      Raise_PE_3 (B); --  @RAISE:FAIL exception propagated from ignored ghost context to checked ghost context
      pragma Assert (Runtime => not B);
   exception
      when Program_Error =>
         null;
   end Catch_PE_3;

   procedure Raise_PE_4
   with Ghost => Runtime, Exceptional_Cases => (Program_Error => True), No_Return
   is
   begin
      raise Program_Error;
   end Raise_PE_4;

   procedure Catch_PE_4 with Ghost, Post => True is
   begin
      Raise_PE_4; --  OK: exception propagated from checked ghost context to ignored ghost context
   exception
      when Program_Error =>
         null;
   end Catch_PE_4;

   procedure Raise_PE_5 (B : Boolean)
   with Ghost => L1, Exceptional_Cases => (Program_Error => B), Post => not B
   is
   begin
      if B then
         raise Program_Error;
      end if;
   end Raise_PE_5;

   procedure Catch_PE_5 (B : Boolean) with Ghost => L2, Post => True is
   begin
      Raise_PE_5 (B); --  OK: exception propagated from dependent ghost level
      pragma Assert (Runtime => not B);
   exception
      when Program_Error =>
         null;
   end Catch_PE_5;
begin
   Catch_PE (True);
end Main;
