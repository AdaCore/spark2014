with Tagged_DIC; use Tagged_DIC;

package Extensions is pragma Elaborate_Body;
   type Priv_Ext is new Root with private;

   function Gimme_One return Priv_Ext;

   type Pub_Ext is new Root with record
      Y : Integer;
   end record;

   function Gimme_One return Pub_Ext;

   type Illegal is new Root_2 with private
     with Default_Initial_Condition;

   function Gimme_One return Illegal;
private
   type Priv_Ext is new Root with record
      Y, Z : Integer;
   end record;

   type Illegal is new Root_2 with record
      Y, Z : Integer := 0;
   end record;
end Extensions;
