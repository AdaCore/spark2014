package body P is

   procedure Proc (Arg : T) is
      type Proxy is new T (Arg.Discr);

      Obj : Proxy;

      procedure Nested
        with Global => (Input => Obj),
             Pre    => Obj.Discr = 0
      is
         Loc : Proxy;
      begin
         Loc := Obj;
      end Nested;
   begin
      null;
   end Proc;

end;
