pragma SPARK_Mode;

-- This is a test for [K331-010] the introduction of the language profile KCG
-- and the extend accept annotation which permits the use of "all" in place
-- of specific variable names when the -language=KCG is selected.
package body Applies_To_All is

   --# accept F, 501, all, "KCG";
      -- Allowed when -language=kcg
   --# accept F, 602, all, "KCG";
      -- otherwise semantic error 175

   package P_1 is
      procedure Proc (B : in Boolean; X : out Integer)
         with Depends => (X => B);
   end P_1;

   package P_2 is
      procedure Proc (B : in Boolean; X : out Integer)
         with Depends => (X => B);
   end P_2;

   package body P_1 is separate;

   package body P_2 is separate;

   procedure Proc_1 (B : in Boolean; X : out Integer)
   is
      Loc : Integer;
   begin
      if B then
         Loc := 42;
      end if;
      X := Loc;  -- Flow eror justified if -language=kcg
                 -- otherwise flow error 501
   end Proc_1;   -- Flow error justified if -language=kcg
                 -- otherwise flow error 602

   procedure Proc_2 (B : in Boolean; X : out Integer)
      with Depends => (X => B)
   is
      Loc : Integer;
      procedure Proc_2_1
         with Global  => (Input  => B, Output => (Loc, X)),
              Depends => ((Loc, X) => B)
      is
      begin
         if B then
            Loc := 42;
         end if;
         X := Loc;  -- Flow eror justified if -language=kcg
                    -- otherwise flow error 501
      end Proc_2_1; -- Flow errors justified if -language=kcg
                    -- otherwise flow errors 602 on X and Loc
                    -- Flow errors 10 and 33 in all cases
   begin
      Proc_2_1;
   end Proc_2;

   procedure Proc_3 (B : in Boolean; X : out Integer)
      with Depends => (X => B)
   is
      --# accept F, 501, all, "OK";
         -- Allowed when -language=kcg
                                     -- otherwise semantic error 175
   begin
      if B then
         X := 42;
      else
         X := 47;
      end if;
   end Proc_3;  -- No errors found if -language=kcg

   procedure Proc_4 (B : in Boolean; X : out Integer)
      with Depends => (X => B)
   is
      Loc : Integer;
   begin
      if B then     -- Flow error 10: ineffective statement
         Loc := 42; -- Flow error 10: ineffective statement
      else
         Loc := 47; -- Flow error 10: ineffective statement
      end if;
   end Proc_4;      -- Flow errors 35, 32, 31, 50

   procedure Proc_5 (B : in Boolean; X : out Integer)
      with Depends => (X => B)
   is
      package P is
         procedure Proc_5_1 (B : in Boolean; X : out Integer)
            with Depends => (X => B);
      end P;

      package body P is
         procedure Proc_5_1 (B : in Boolean; X : out Integer)
         is
            Loc : Integer;
         begin
            if B then
               Loc := 42;
            end if;
            X := Loc;   -- Errors justified if -language=kcg
                        -- otherwise flow error 501
         end Proc_5_1;  -- Errors justified if -language=kcg
                        -- otherwise flow error 602
      end P;

   begin
      P.Proc_5_1 (B, X);
   end Proc_5;

   procedure Proc_6 (B : in Boolean; X : out Integer)
               is separate
                     with Refined_Depends => (X => B);

   procedure Proc_7 (B : in Boolean; X : out Integer)
               is separate
                     with Refined_Depends => (X => B);

   procedure Proc_8 (B : in Boolean; X : out Integer)
      with Depends => (X => B)
   is
      procedure P_8_1 (B : in Boolean; X : out Integer)
         with Depends => (X => B)
      is
         procedure P_8_2
            with Global  => (Input  => B, Output => X),
                 Depends => (X => B)
         is
            Loc : Integer;
         begin
            if B then
               Loc := 42;
            end if;
            X := Loc;
         end P_8_2;
      begin
         P_8_2;
      end P_8_1;
   begin
      P_8_1 (B, X);
   end Proc_8;


end Applies_To_All;
