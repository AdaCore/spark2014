package body Vk is

   package body Tag is

      procedure Set_Name (This  : in out T;
                          Value : String) is
      begin
         Name_P.Initialize (This => This.My_Name,
                            Text => Value);
      end Set_Name;

   end Tag;

end Vk;
