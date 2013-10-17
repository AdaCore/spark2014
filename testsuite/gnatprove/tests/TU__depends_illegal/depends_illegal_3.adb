with Depends_Illegal_3_Helper;
use  Depends_Illegal_3_Helper;

package body Depends_Illegal_3
  with SPARK_Mode
is
   procedure P1 (Par1 : in out Integer ; Par2 : in Integer)
     --  TU: 16. A ``dependency_clause`` with a "+" symbol in the syntax
     --  ``output_list`` =>+ ``input_list`` means that each ``output`` in
     --  the ``output_list`` has a *self-dependency*, that is, it is
     --  dependent on itself. [The text (A, B, C) =>+ Z is shorthand for
     --  (A => (A, Z), B => (B, Z), C => (C, Z)).]
     with Global  => (In_Out => X,
                      Input  => Y),
          Depends => ((X, Par1) =>+ (Par2, Y))
   is
   begin
      X    := Par2 + Y;
      Par1 := Par1 - Y;
   end P1;


   procedure P2 (Par1, Par2 : out Integer)
     --  TU: 18. A ``dependency_clause`` with a **null** ``input_list`` means
     --  that the final value of the entity denoted by each ``output`` in the
     --  ``output_list`` does not depend on any member of the input set of
     --  the subprogram (other than itself, if the ``output_list`` =>+
     --  **null** self-dependency syntax is used).
     with Global  => (Output => X),
          Depends => ((Par1, Par2, X) => null)
   is
   begin
      X    := Par2;  --  X should Depend on nothing
      Par1 := Par2;  --  Par1 should Depend on nothing
   end P2;


   procedure P3 (Par1 : Integer ; Par2 : in out Integer)
     --  TU: 19. The ``inputs`` in the ``input_list`` of a
     --  ``null_dependency_clause`` may be read by the subprogram but play
     --  no role in determining the values of any outputs of the subprogram.
     with Global  => (Input  => X,
                      In_Out => Y),
          Depends => ((Par2, Y) => null,
                      null      => (Par1, Par2, X, Y))
   is
   begin
      null;
   end P3;


   procedure P4
     --  TU: 20. A Depends aspect of a subprogram with a **null**
     --  ``dependency_relation`` indicates that the subprogram has no
     --  ``inputs`` or ``outputs``. [From an information flow analysis
     --  viewpoint it is a null operation (a no-op).]
     with Depends => null
   is
   begin
      X := 10;
   end P4;


   procedure P5 (P1 :        Integer;
                 P2 :    out Integer;
                 P3 : in out Integer)
     --  TU: 22. A procedure without an explicit Depends aspect specification
     --  has a default ``dependency_relation`` that each member of its output
     --  set is dependent on every member of its input set. [This conservative
     --  approximation may be improved by analyzing the body of the
     --  subprogram if it is present.]
     with Global  => (Input  => G_Var1,
                      Output => G_Var2,
                      In_Out => G_Var3),
          Depends => (P2     => P1,
                      P3     => P3,
                      G_Var2 => G_Var1,
                      G_Var3 => G_Var3)
     --  The correct Depends aspect would have been:
     --     Depends => ((P2,
     --                  P3,
     --                  G_Var2,
     --                  G_Var3) => (P1,
     --                              P3,
     --                              G_Var1,
     --                              G_Var3))
   is
   begin
      Implicit_Depends (P1, P2, P3);
   end P5;


   function F1 (Par1 : Natural) return Natural
     --  TU: 11. For the purposes of determining the legality of a Result
     --  ``attribute_reference``, a ``dependency_relation`` is considered
     --  to be a postcondition of the function to which the enclosing
     --  ``aspect_specification`` applies.
     with Depends => (F1'Result => null,
                      null      => Par1)
   is
   begin
      return Par1;
   end F1;
end Depends_Illegal_3;
