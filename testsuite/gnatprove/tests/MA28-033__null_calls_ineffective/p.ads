with Logging;
package P
  with SPARK_Mode  
is
   --  See bodies of these procedures for expected results
   
   procedure Op1 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C));
   
   procedure Op2 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C));
   
   procedure Op3 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C));
   
   procedure Op4 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C));
   

   procedure Op5 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C));
   
   procedure Op6 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => (Output => Logging.TestPoint),
          Depends => (D                 => (A, B, C),
                      Logging.TestPoint => A);
   
   procedure Op7 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => null,
          Depends => (D => (A, B, C));

   procedure Op8 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global  => (Output => Logging.TestPoint),
          Depends => (D                 => (A, B, C),
                      Logging.TestPoint => A);
   
   procedure Op9 (A : in     Integer;
		  B : in     Boolean;
		  C : in     Character;
		  D :    out Integer)
     with Global => null,
          Depends => (D => (A, B, C));

   procedure Op10 (A : in     Integer;
		   B : in     Boolean;
		   C : in     Character;
		   D :    out Integer)
     with Global => null,
          Depends => (D => (A, B, C));

end P;
