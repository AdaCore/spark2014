package Enumrep is

   package HAL is
      package Filesystem is
         type Status_Code is
           (OK,
            Non_Empty_Directory,
            Disk_Error,
            Disk_Full);
      end Filesystem;
   end HAL;

   type Status_Code is
     (OK,
      Non_Empty_Directory,
      Disk_Error,
      Disk_Full);

   for Status_Code use
     (OK                      => HAL.Filesystem.OK'Enum_Rep,
      Non_Empty_Directory     => HAL.Filesystem.Non_Empty_Directory'Enum_Rep,
      Disk_Error              => HAL.Filesystem.Disk_Error'Enum_Rep,
      Disk_Full               => HAL.Filesystem.Disk_Full'Enum_Rep);

end Enumrep;
