pragma Extensions_Allowed (On);

procedure Test_Marking with SPARK_Mode is

   function F (X : in out Integer) return Integer
     with Side_Effects,
          Pre => X < Integer'Last,
          Post => X = X'Old + 1
            and then F'Result = X
   is
   begin
      X := X + 1;
      return X;
   end F;

   procedure Test_OK1 is
      X : Integer := 0;
   begin
      Y : Integer := F (X);
   end Test_OK1;

   procedure Test_OK2 (B : Boolean) is
      X : Integer := 0;
   begin
      if B then
         Y : Integer := F (X);
      else
         Y : Integer := F (X);
      end if;
   end Test_OK2;

   procedure Test_OK3 (B1, B2 : Boolean) is
      X : Integer := 0;
   begin
      if B1 then
         Y : Integer := F (X);
      elsif B2 then
         Y : Integer := F (X);
      else
         Y : Integer := F (X);
      end if;
   end Test_OK3;

   procedure Test_OK4 (C : Integer) is
      X : Integer := 0;
   begin
      case C is
      when 0 =>
         Y : Integer := F (X);
      when 1 =>
         Y : Integer := F (X);
      when others =>
         Y : Integer := F (X);
      end case;
   end Test_OK4;

   procedure Test_OK5 (C : Integer) is
      X : Integer := 0;
   begin
      raise Program_Error;
   exception
      when Program_Error =>
         Y : Integer := F (X);
   end Test_OK5;

   procedure Test_OK6 is
      X : Integer := 0;
   begin
      declare
         Z : Integer := 1;
      begin
         Y : Integer := F (X);
      end;
   end Test_OK6;

   procedure Test_OK7 is
      X : Integer := 0;
   begin
      while True loop
         Y : Integer := F (X);
      end loop;
   end Test_OK7;

   procedure Test_KO1 is
      X : Integer := 0;
      Y : Integer := F (X);
   begin
      null;
   end Test_Ko1;

   procedure Test_KO2 is
      X : Integer := 0;
   begin
      declare
         Y : Integer := F (X);
      begin
         null;
      end;
   end Test_KO2;

   procedure Test_KO3 is
      X : Integer := 0;
      Z : Integer;
   begin
      Z :=
        (declare
           Y : constant Integer := F (X);
         begin Y);
   end Test_KO3;

begin
   null;
end Test_Marking;
