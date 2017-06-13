package body Type_Implicit is

   task body Worker is
      Message : Message_Type;
   begin
      loop
         Mailbox.Get_Message(Message);
         case Message is
            when Step =>
               -- Process the Step message...
               null;

            when Reset =>
               -- Process the Reset message...
               null;
         end case;
      end loop;
   end;

end;
