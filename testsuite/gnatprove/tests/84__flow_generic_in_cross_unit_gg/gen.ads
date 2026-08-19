package Gen is

   generic
      type T is private;
      C : T;
   procedure Generic_P (R : out T)
      with Global => (Input => C);

end;
