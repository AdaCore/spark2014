package P
  with SPARK_Mode  
is
      
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
   
end P;
