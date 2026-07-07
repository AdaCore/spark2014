
--  Test accounting of function with side effects in frame condition generation

procedure Frame_Condition with SPARK_Mode is

   E : exception;
   X : Integer;
   function Writes return Boolean
     with Side_Effects,
     Global => (In_Out => X),
     Import,
     Post => (X = X'Old + 1);
   function Writes (Y : in out Integer) return Boolean
     with Side_Effects,
     Global => null,
     Import,
     Post => (Y = Y'Old + 1);
   function May_Raise return Boolean
     with Side_Effects,
     Global => (In_Out => X),
     Import,
     Post => (X = X'Old + 1),
     Exceptional_Cases => (E => True);
   function May_Raise (Y : in out Integer) return Boolean
     with Side_Effects,
     Import,
     Exceptional_Cases => (E => True);
   function Pure_Raise return Boolean
     with Side_Effects,
     Import,
     Exceptional_Cases => (E => True);

   function Random (X : Integer) return Boolean with Import, Global => null;

   procedure Test_If_1 is
      X_Old : Integer := X;
      Y : Integer := 0;
   begin
      while Random (X) loop
         pragma Loop_Invariant (True);
         begin
            if May_Raise then
               Y := Y + 1;
            end if;
         exception
            when E =>
               null;
         end;
      end loop;
      pragma Assert (X = X_Old); --@ASSERT:FAIL
   end Test_If_1;

   procedure Test_If_2 is
      Y : Integer := 0;
   begin
      while Random (X) loop
         begin
            if May_Raise then
               null;
            end if;
         exception
            when E =>
               Y := Y + 1;
         end;
      end loop;
      pragma Assert (Y = 0); --@ASSERT:FAIL
   end Test_If_2;

   procedure Test_If_3 with Global => null;
   procedure Test_If_3 is
      Y : Integer := 0;
      Z : Integer := 0;
   begin
      while Random (Y) loop
         begin
            if (if Y /= 0 then Pure_Raise else Writes (Y)) then
               null;
            end if;
         exception
            when E =>
               exit when Writes (Z);
               raise E;
         end;
      end loop;
      pragma Assert (Z = 0 or Z = 1); --@ASSERT:PASS
      pragma Assert (Y = 0); --@ASSERT:FAIL
   exception
      when E =>
         null;
   end Test_If_3;

   procedure Test_Case_1 is
      Y : Integer := 0;
   begin
      while Random (Y) loop
         case Writes (Y) is
            when True =>
               exit;
            when others =>
               null;
         end case;
      end loop;
      pragma Assert (Y = 0); --@ASSERT:FAIL
   end Test_Case_1;

begin
   null;
end Frame_Condition;
