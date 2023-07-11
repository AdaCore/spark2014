package body Hidden is
   Variable : Integer := 0;
   Input : constant Integer := Variable;
   function Proxy return Integer is (Input);
end;
