with Interfaces.C;

package Messages
   with Spark_Mode => On
is

   type Node_Id_Type         is new Interfaces.C.unsigned_short;
   type Sequence_Number_Type is new Interfaces.C.unsigned_long;

   function Compute_Fletcher_Checksum
     (Buffer : in Interfaces.C.char_array;
      Size   : in Interfaces.C.size_t) return Interfaces.C.unsigned_short
     with
       Global => null,
       Import => True,
       Convention => C,
       Pre => Size = Buffer'Length,
       External_Name => "compute_fletcher_checksum";

   type Packet_Header_Type is
      record
         Source_Node : Node_Id_Type;
         Destination_Node : Node_Id_Type;
         Sequence_Number : Sequence_Number_Type;
      end record
   with Convention => C;

   type Error_Code is (Success, Invalid_Destination, Insufficient_Space)
      with Convention => C;
      for Error_Code use (1, 2, 3);

   -- function Install_Header
   --   (Buffer : in out Interfaces.C.char_array;
   --    Size   : in  Interfaces.C.size_t;
   --    Header : in  Packet_Header_Type) return Error_Code
   --   with
   --     Global => null,
   --     Import => True,
   --     Convention => C,
   --     External_Name => "install_header";

   -- Needed to make operators used in postcondition directly visible.
   use type Interfaces.C.size_t;
   use type Interfaces.C.char;
   use type Interfaces.C.char_array;
   procedure Install_Header (Buffer : in out Interfaces.C.char_array;
                             Size   : in     Interfaces.C.size_t;
                             Header : in     Packet_Header_Type;
                             Status :    out Error_Code)
      with
         Global  => null,
         Depends => (Buffer =>+ (Size, Header), Status => (Size, Header)),
         Post    => (if Status /= Success then
                        Buffer = Buffer'Old
                     else
                       (for all J in Buffer'First + 12 .. Buffer'Last =>
                                Buffer(J) = Buffer'Old (J))),
         Import        => True,
         Convention    => C,
         External_Name => "install_header_helper";
end Messages;
