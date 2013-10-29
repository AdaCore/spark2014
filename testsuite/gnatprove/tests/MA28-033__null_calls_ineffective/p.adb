with P.Logging;
package body P
  with SPARK_Mode  
is
   
   procedure Op1 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer) is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);
      -- No logging - should be fine.
   end Op1;
   
   procedure Op2 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer) is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Call Logging.Trace directly
      --  Should this call be marked as "ineffective"??
      Logging.Trace (A, B, C);
   end Op2;
   
   procedure Op3 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer) is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Call Logging.Trace via pragma Debug
      --  This call should be ignored
      pragma Debug (Logging.Trace (A, B, C));
   end Op3;
   
   procedure Op4 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer) is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Explicit null statement - should not be ineffective.
      null;
   end Op4;
   
end P;
