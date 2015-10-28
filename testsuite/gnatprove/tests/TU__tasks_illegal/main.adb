with PO_T6; use PO_T6;

procedure Main
  --  TU: 8. A ``global_item`` occurring in the Global aspect specification of
  --  the main subprogram shall not denote an object or state abstraction whose
  --  Part_Of aspect denotes a task or protected unit. [In other words, the
  --  environment task cannot reference objects which "belong" to other tasks.]
  with Global => (In_Out => The_Protected_Int)
is
begin
   The_Protected_Int := P_Int.Get + 1;
end Main;
