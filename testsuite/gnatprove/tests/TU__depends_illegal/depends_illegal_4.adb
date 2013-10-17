package body Depends_Illegal_4
  with SPARK_Mode
is
   X, Y : Natural := 1;  --  The package should not have any state.


   procedure P1 (Par1 :        Natural;
                 Par2 :    out Natural;
                 Par3 : in out Natural)
     --  TU: 23. Each entity denoted by an ``output`` given in the Depends
     --  aspect of a subprogram must be an output in the implementation of the
     --  subprogram body and the output must depend on all, but only, the
     --  entities denoted by the ``inputs`` given in the ``input_list``
     --  associated with the ``output``.
     with Depends => (Par2 => (Par1, X),
                      Par3 => (Par3, X, Y),
                      Y    => null)
   is
   begin
      Par2 := Par1 + X + Y;
      Par3 := Par3 + X;
   end P1;


   procedure P2 (Par1 : out Natural)
     --  TU: 24. Each output of the implementation of the subprogram body is
     --  denoted by an ``output`` in the Depends aspect of the subprogram.
     with Depends => (Par1 => null)
   is
   begin
      Par1 := 0;
      X    := 1;
   end P2;


   procedure P3 (Par1, Par2 : in out Natural)
     --  TU: 25. Each input of the implementation of a subprogram body is
     --  denoted by an ``input`` of the Depends aspect of the subprogram.
     with Depends => (Par1 => (Par1, X),
                      Par2 => Par2)
   is
   begin
      Par1 := X + Par1 + Par2;
      Par2 := Y + Par2;
   end P3;
end Depends_Illegal_4;
