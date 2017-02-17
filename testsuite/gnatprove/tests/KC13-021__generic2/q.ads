with P;
pragma Elaborate_All(P);
package Q is

   function QF1 (J : Integer) return Integer;
   procedure QP1 (J : in out Integer) with
     Pre => J < Integer'Last;

   package P1 is new P (1, 2, 3, 4, Integer, Boolean, Natural, QF1, QP1);

   procedure QP (X1 : Boolean; X2 : Integer; X3 : Natural; X4 : out Integer);

end;
