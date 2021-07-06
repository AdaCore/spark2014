procedure Main with SPARK_Mode is
   function Do_Something (B : Boolean) return Boolean is
   begin
      return (case B is
                 when True  =>
                (case B is
                    when True  => False,
                    when False => raise Program_Error),
                 when False => True);
   end Do_Something;
begin
   null;
end Main;
