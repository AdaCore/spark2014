with Ghost_Example; use Ghost_Example;

package body Client_Unit is

   procedure Bad_Client is
      Item1_Done, Item2_Done : Boolean;
   begin
      Reset;
      Init (Item1_Done);
      if Item1_Done then
         First_Work_Item (Item2_Done);
      else
         Reset;
      end if;
      if Item1_Done then
         Second_Work_Item (Item2_Done);
      else
         Reset;
      end if;
   end Bad_Client;

   procedure Good_Client is
      Item_Done : Boolean;
   begin
      Reset;
      Init (Item_Done);
      if Item_Done then
         First_Work_Item (Item_Done);
         if Item_Done then
            Second_Work_Item (Item_Done);
            if not Item_Done then
               Reset;
            end if;
         else
            Reset;
         end if;
      else
         Reset;
      end if;
   end Good_Client;

   procedure Another_Good_Client is
      Item_Done : Boolean;
   begin
      Reset;
      Init (Item_Done);
      if Item_Done then
         First_Work_Item (Item_Done);
      end if;
      if Item_Done then
         Second_Work_Item (Item_Done);
      end if;
      if not Item_Done then
         Reset;
      end if;
   end Another_Good_Client;

   procedure Yet_Another_Good_Client is
      Item_Done : Boolean;
   begin
      Reset;
      Init (Item_Done);
      if Item_Done then
         First_Work_Item (Item_Done);
      else
         Reset;
      end if;
      if Item_Done then
         Second_Work_Item (Item_Done);
      else
         Reset;
      end if;
      if not Item_Done then
         Reset;
      end if;
   end Yet_Another_Good_Client;


end Client_Unit;
