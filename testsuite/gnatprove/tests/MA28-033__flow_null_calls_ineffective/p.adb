with Logging;
package body P is

   procedure Op1 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C))
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);
      -- No logging - should be fine.
   end Op1;

   procedure Op2 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
                  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C))
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Call Logging.Trace3 directly
      --  Should NOT be ineffective as A, B, C all go to null.
      Logging.Trace3 (A, B, C);
   end Op2;

   procedure Op3 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
                  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C))
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Call Logging.Trace via pragma Debug
      --  This call should be ignored completely
      pragma Debug (Logging.Trace3 (A, B, C));
   end Op3;

   procedure Op4 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
                  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C))
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Explicit null statement - should not be ineffective.
      null;
   end Op4;

   procedure Op5 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
                  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C))
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Call Logging.Trace1 directly
      --  Should NOT be ineffective as A goes to null.
      Logging.Trace1 (A);
   end Op5;

   procedure Op6 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
                  D :    out Integer)
     with Global  => (Output => Logging.TestPoint),
          Depends => (D                 => (A, B, C),
                      Logging.TestPoint => A)
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Call Logging.Trace_Mixed directly
      --  NOT ineffective, since B goes to null
      --  and A goes to Logging.TestPoint
      Logging.Trace_Mixed (A, B);
   end Op6;

   procedure Op7 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
                  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C))
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Call Logging.Trace1 directly
      --  TWO calls - neither should be marked as ineffective
      Logging.Trace1 (A);
      Logging.Trace1 (A+1);
   end Op7;

   procedure Op8 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
                  D :    out Integer)
     with Global  => (Output => Logging.TestPoint),
          Depends => (D                 => (A, B, C),
                      Logging.TestPoint => A)
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      --  Call Logging.Trace_Mixed directly
      --  TWO calls in sequence. First assignment to Logging.TestPoint
      --  IS ineffective.  Assignments from B to "null" are
      --  NOT ineffective
      Logging.Trace_Mixed (A, B);
      Logging.Trace_Mixed (A+1, B);
   end Op8;

   procedure Op9 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C))
   is
      Tmp : Integer;
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      -- Should NOT be ineffective
      Tmp := A + 1;

      -- Should NOT be ineffective
      Logging.Trace1 (Tmp);
   end Op9;

   procedure Op10 (A : in     Integer;
		   B : in     Boolean;
		   C : in     Character;
		   D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C))
   is
   begin
      D := A + Boolean'Pos (B) + Character'Pos (C);

      -- Should NOT be ineffective
      if A > 10 then
         -- Should NOT be ineffective
         Logging.Trace1 (A + 5);
      else
         -- Should NOT be ineffective
         Logging.Trace1 (A - 5);
      end if;
   end Op10;

   procedure Op11 (A : in     Integer;
                   B : in     Integer;
                   X :    out Integer)
     with Global  => null,
          Depends => (X => A,
                      null => B)
   is
   begin
      X := A;
      Logging.Trace1 (B);
   end Op11;

   procedure Op12 (A : in     Integer;
                   B : in     Integer;
                   X :    out Integer)
     with Global  => null,
     Depends => (X => A,
                 null => B)
   is
   begin
      Op11 (A, B, X);
   end Op12;

end P;
