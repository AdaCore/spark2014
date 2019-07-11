with FIS;

package FDP is
   type Kind is
      (Undefined,
       Flight_Data_Msg);

   type T is private;

   Undefined_Request : constant T;

private

   type T (The_Kind : Kind := Undefined) is
      record
         case The_Kind is

            when Flight_Data_Msg =>
               Flight_Data_Msg_Data : FIS.Data;

            when others =>
               null;

         end case;
      end record;

   Undefined_Request : constant T := T'(The_Kind => Undefined);

end FDP;
