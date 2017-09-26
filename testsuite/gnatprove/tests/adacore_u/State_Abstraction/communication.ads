with Abstraction_Ext; use Abstraction_Ext;
pragma Elaborate_All(Abstraction_Ext);
package Communication with SPARK_Mode,
  Abstract_State => State,
  Initializes    => (State => V_Ext)
is
   type Data is new Integer;
   type Mailbox is private;
   function  Create  (Address : String; Port : Natural) return Mailbox;
   procedure Send    (Message :     Data; To : in out Mailbox);
   procedure Receive (Message : out Data; To : in out Mailbox);
private
   package Ring_Buffer
     with Initializes => (Max => V_Ext)
   is
      type Buffer is private with Default_Initial_Condition;
      procedure Enqueue (E :     Data; B : in out Buffer);
      procedure Dequeue (E : out Data; B : in out Buffer);
      Max : constant Natural := V_Ext with Part_Of => State;
   private
      type Data_Array is array (Positive range 1 .. Max) of Data;
      type Buffer is record
         Content : Data_Array;
         First   : Positive := 1;
         Length  : Natural := 0;
      end record;
   end Ring_Buffer;
   type Mailbox is record
      Address    : String (1 .. 15) := "000.000.000.000";
      Port       : Natural := 0;
      In_Buffer  : Ring_Buffer.Buffer;
      Out_Buffer : Ring_Buffer.Buffer;
   end record;
end Communication;
