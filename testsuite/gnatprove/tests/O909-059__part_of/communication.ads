with Abstraction_Ext; use Abstraction_Ext;

package Communication with SPARK_Mode,
   Abstract_State => State,
   Initializes => (State => V_Ext)
is
   type Mailbox is private;
   procedure P;

private
   Max1 : constant Natural := V_Ext; -- needs Part_Of
   Max2 : constant Natural := V_Ext; -- needs Part_Of
   package Ring_Buffer
     with Abstract_State => (Bla with Part_Of => State)
   is
      Max3 : constant Natural := V_Ext; -- needs Part_Of
      Max4 : constant Natural := V_Ext; -- needs Part_Of
      Max5 : constant Natural;
   private
      Max5 : constant Natural := V_Ext; -- doesn't need Part_Of because deferred
      package R
        with Abstract_State => (Bla2 with Part_Of => Bla)
      is
         Max6 : constant Natural := V_Ext; -- needs Part_Of
         package Q is
            Max7 : constant Natural := V_Ext; -- needs Part_Of
            package S is
               Max8 : constant Natural := V_Ext; -- needs Part_Of
               Max9 : constant Natural := V_Ext; -- needs Part_Of
            end S;
         end Q;
      end R;
   end Ring_Buffer;

   type Mailbox is record
      Address    : String (1 .. 15);
   end record;

end Communication;
