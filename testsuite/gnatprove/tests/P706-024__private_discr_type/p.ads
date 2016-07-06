with Dev;

package P is

   type Frame_Buffer is limited
      new Dev.Device with private;

private

   Port : aliased Integer;

   type Frame_Buffer
   is limited new Dev.Device with record
      D : Dev.Device (Port'Access);
   end record;

end P;
