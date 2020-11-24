package body P with
   SPARK_Mode
is
   --  The following hierarchy of nested packages:
   --    X -> Y -> Z
   --  has a corresponding hierarchy of abstract states:
   --    channel_x -> channel_y -> channel_z
   --  which is initialized by a hierarchy of procedure calls:
   --    init_x -> init_y -> init_z.
   --
   --  This mimics a similar hierarchy of child package in the original test.
   --
   --  The final procedure has explicit flow contracts and body either
   --  unavailable (in the original test) or hidden begin SPARK_Mode => Off
   --  (here). The commened contract on init_y is a workaround for the crash
   --  from the original test.

   package X with
      Abstract_State => channel_x
   is
      procedure init_x;
   private
      package Y with
         Abstract_State => (channel_y with Part_Of => X.channel_x)
      is
         procedure init_y; -- with Global => (output => channel);
      private
         package Z with
            Abstract_State => (channel_z with Part_Of => Y.channel_y)
         is
            procedure init_z with
               Global  => (Output => channel_z),
               Depends => (channel_z => null);
         end Z;
      end Y;
   end X;

   package body X with
      Refined_State => (channel_x => Y.channel_y)
   is
      package body Y with
         Refined_State => (channel_y => Z.channel_z)
      is
         package body Z with
            Refined_State => (channel_z => Dummy)
         is
            Dummy : Integer;
            procedure init_z with
               SPARK_Mode => Off
            is
            begin
               Dummy := 0;
            end init_z;
         end Z;
         procedure init_y is
         begin
            -- Init private child
            Z.init_z;
         end init_y;
      end Y;
      procedure init_x is
      begin
         Y.init_y;
      end init_x;
   end X;

   package body Application is
      procedure init is
      begin
         X.init_x;
      end init;
   end Application;
end P;
