package Q is

   task type TT;

   TO1, TO2 : TT; --  multiple tasks will block on P.PO1.E

end;
