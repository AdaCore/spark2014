package B
is
   function Get return Boolean;
private

   State : Boolean := False;

   function Get return Boolean is (State);

end B;
