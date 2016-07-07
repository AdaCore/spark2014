with STM32.GPIO; use STM32.GPIO;

package body Framebuffer_ILI9341 is

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
   is
   begin
      Set (LCD_CSX);
   end Initialize;

end Framebuffer_ILI9341;
