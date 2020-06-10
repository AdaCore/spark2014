package body P is

   procedure Copy (Source : in     String;
                   Target :    out Str)
   is
      --  pragma Annotate
      --    (GNATprove, Intentional,
      --     """Target.Value"" might not be initialized*",
      --     "Value is always initialized up to Length");
   begin
      Target.Length := 0;
      if Source'Length <= Str_Length'Last then
         Target.Length := Source'Length;
         Target.Value (1 .. Target.Length) := Source;
      end if;
   end Copy;

end P;
