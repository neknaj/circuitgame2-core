/* Pico 2 のフラッシュとメイン SRAM。 */
MEMORY {
    FLASH : ORIGIN = 0x10000000, LENGTH = 4096K
    RAM   : ORIGIN = 0x20000000, LENGTH = 512K
}

/* ブート ROM がベクターテーブルの直後からイメージ定義を読めるようにする。 */
SECTIONS {
    .start_block : ALIGN(4) {
        KEEP(*(.start_block));
    } > FLASH
} INSERT AFTER .vector_table;

_stext = ADDR(.start_block) + SIZEOF(.start_block);
