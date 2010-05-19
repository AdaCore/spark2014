-- The 1553 bus interface for the Bus Controller (BC)
--
-- $Id: bc1553.adb,v 1.1.1.1 2004/01/12 19:29:12 adi Exp $
--
-- $Log: bc1553.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.6  2003/08/17 22:06:31  adi
-- Added lru_number
--
-- Revision 1.5  2003/02/12 21:22:37  adi
-- Added set_message_valid
--
-- Revision 1.4  2003/02/11 20:14:35  adi
-- Added fresh and valid checking functions
--
-- Revision 1.3  2003/02/05 22:49:10  adi
-- Fixed for renamed types
--
-- Revision 1.2  2003/02/03 23:17:30  adi
-- Added Acknowledge_Message body
--
-- Revision 1.1  2003/02/03 18:26:34  adi
-- Initial revision
--
--
package body BC1553
is
   -- Convert LRU names to LRU indices
   type Lru_Table is array(Lru_Name) of Bus.Lru_Index;
   Lru_Names : constant Lru_Table
     := Lru_Table'(Barometer => 1,
                   Asi      => 2,
                   Ins      => 3,
                   Compass  => 4,
                   Fuel     => 5,
                   Fuze     => 6,
                   Radar    => 7,
                   Infrared => 8,
                   Fins     => 9,
                   Motor    => 10,
                   Destruct => 11,
                   Warhead  => 12);

   function Lru_Number(L : Lru_Name) return Bus.Lru_Index
   is begin
      return Lru_Names(L);
   end Lru_Number;


   -- Write out data to the RTs

   procedure Set_Message_Valid(Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                               Dest    : in Lru_Name)
   is
   begin
      Bus.Set_RT_Message_Valid(Subaddress_Idx => Subaddress_Idx,
                               Dest => Lru_Names(Dest));
   end Set_Message_Valid;

   procedure Write_Word(Data    : in Bus.Word;
                        Idx     : in Bus.Word_Index;
                        Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                        Dest    : in Lru_Name)
   is
   begin
      Bus.Write_RT_Word(Data => Data,
                        Idx => Idx,
                        Subaddress_Idx => Subaddress_Idx,
                        Dest => Lru_Names(Dest));
   end Write_Word;

   procedure Write_Message(Data    : in Bus.Message;
                           Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                           Dest    : in Lru_Name)
   is
   begin
      Bus.Write_Rt_Message(Data => Data,
                           Subaddress_Idx => Subaddress_Idx,
                           Dest => Lru_Names(Dest));
   end Write_Message;

   -- See if a message is fresh
   function Is_Fresh(Src : Lru_Name;
                     Subaddress_Idx : Bus.Lru_Subaddress_Index)
                    return Boolean
   is begin
      return Bus.Is_BC_Fresh(Lru_Names(Src),Subaddress_Idx);
   end Is_Fresh;

   -- See if a message is valid
   function Is_Valid(Src : Lru_Name;
                     Subaddress_Idx : Bus.Lru_Subaddress_Index)
                    return Boolean
   is begin
      return Bus.Is_BC_Valid(Lru_Names(Src),Subaddress_Idx);
   end Is_Valid;


   -- Read data sent to the BC

   procedure Read_Word(Src     : in  Lru_Name;
                       Idx     : in  Bus.Word_Index;
                       Subaddress_Idx : in  Bus.Lru_Subaddress_Index;
                       Data    : out Bus.Word)
   is
   begin
      Bus.Read_BC_Word(Src => Lru_Names(Src),
                       Idx => Idx,
                       Subaddress_Idx => Subaddress_Idx,
                       Data => Data);
   end Read_Word;

   procedure Read_Message(Src     : in  Lru_Name;
                          Subaddress_Idx : in  Bus.Lru_Subaddress_Index;
                          Data    : out Bus.Message)
   is
   begin
      Bus.Read_Bc_Message(Src => Lru_Names(Src),
                          Subaddress_Idx => Subaddress_Idx,
                          Data => Data);
   end Read_Message;

   procedure Acknowledge_Message(Src     : in  Lru_Name;
                                 Subaddress_Idx : in  Bus.Lru_Subaddress_Index)
   is
      Src_Lru : Bus.Lru_Index;
   begin
      Src_Lru := Lru_Names(Src);
      Bus.Acknowledge_Bc_Message(Src => Src_Lru,
                                 Subaddress_Idx => Subaddress_Idx);
   end Acknowledge_Message;

end BC1553;

