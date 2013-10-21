package body Test is

   G : Integer;

   procedure Output_Not_Set (A : Boolean;
                             X : out Integer)
   is
   begin
      if A then
         return;
      end if;
      X := 12;
   end Output_Not_Set;

   procedure Use_Of_Uninitialised (A : Boolean;
                                   X : out Integer)
   is
      N : Integer;
      M : Integer := 8;
   begin
      if A then
         N := 12;
      else
         M := 12;
      end if;
      X := N + M;  -- use of N
   end Use_Of_Uninitialised;

   procedure Extra_Dep (A, B, C : Integer;
                        X, Y    : out Integer)
     with Depends => (X => (A, B),
                      Y => (B, C));

   procedure Extra_Dep (A, B, C : Integer;
                        X, Y    : out Integer)
   is
   begin
      if B > 0 then
         X := A;
         Y := 0;
      else
         X := 0;
         Y := C;
      end if;
      if C > 0 then    --  This is the control dependency
         Y := 0;
      else
         X := 0;       --  And this is why it matters
      end if;
   end Extra_Dep;

   procedure Masked_Code (A : Boolean;
                          X : out Integer)
   is
   begin
      if A then
         X := 8;
      else
         X := 12;
      end if;

      if not A then
         X := 3;
      else
         X := 7;
      end if;
   end Masked_Code;

end Test;
