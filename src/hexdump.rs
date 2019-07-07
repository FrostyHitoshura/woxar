fn hexdump_digits(value: usize, data: &mut [u8]) -> &mut [u8] {
    let mut acc = value;
    let mut idx = data.len();

    while idx != 0 {
        let cur = idx - 1;
        let digit = acc & 0xf;

        data[cur] = {
            if digit < 10 {
                (digit + b'0' as usize) as u8
            } else {
                (digit - 10 + b'A' as usize) as u8
            }
        };

        acc = acc >> 4;

        idx = cur;
    }

    data
}

fn hexdump_ascii(raw_output: &mut Vec<u8>, ascii: &[u8]) {
    if ascii.len() == 0 {
        return;
    }

    // Output separator, ASCII display and finally end of line
    raw_output.push(b' ');
    raw_output.push(b'|');
    raw_output.extend(ascii.iter());
    raw_output.push(b'|');
}

// XXX: Fix output when "offset % 16 != 0"
fn hexdump(offset: usize, data: &[u8]) {
    const SEP: &[u8] = b"  ";
    const ROW_SIZE: usize = 16;
    const SEP_COL_SIZE: usize = 2 /* sep.len() */;
    const HEX_SEP_SIZE: usize = 1;
    const ADDR_COL_SIZE: usize = 8;
    const HEX_COL_SIZE: usize = ROW_SIZE * 3;
    const ASCII_COL_SIZE: usize = ROW_SIZE + 2;
    const ENTER_COL_SIZE: usize = 1;

    let mut idx = 0_usize;
    let row_count = data.len() / ROW_SIZE + {
        if data.len() % ROW_SIZE == 0 {
            1
        } else {
            0
        }
    };
    let mut raw_output = Vec::<u8>::with_capacity(
        row_count
            * (ADDR_COL_SIZE
                + SEP_COL_SIZE
                + HEX_COL_SIZE
                + HEX_SEP_SIZE
                + SEP_COL_SIZE
                + ASCII_COL_SIZE
                + ENTER_COL_SIZE),
    );
    let scratch: &mut [u8] = &mut [0; 8];
    let mut ascii_staged = 0_usize;
    let ascii: &mut [u8] = &mut [0; ROW_SIZE];

    while idx < data.len() {
        let byte = data[idx];
        let idx_in_line = idx % ROW_SIZE;

        // Beginning of a line
        if idx_in_line == 0 {
            // End of a previous line
            if idx != 0 && ascii_staged != 0 {
                hexdump_ascii(&mut raw_output, &ascii[..ascii_staged]);
                raw_output.push(b'\n');

                ascii_staged = 0;
            }

            // Output offset and column separator
            raw_output.extend(hexdump_digits(offset + idx, &mut scratch[0..8]).iter());
            raw_output.extend(SEP.iter());
        }

        // Column that divide the hex output
        if idx_in_line == ROW_SIZE / 2 {
            raw_output.push(b' ');
        }

        // Output data hex and separator
        raw_output.extend(hexdump_digits(byte as usize, &mut scratch[0..2]).iter());
        raw_output.push(b' ');

        // Stage ASCII display
        ascii[idx_in_line] = {
            if byte >= 32 && byte < 127 {
                byte
            } else {
                b'.'
            }
        };

        ascii_staged = ascii_staged + 1;
        idx = idx + 1;
    }

    hexdump_ascii(&mut raw_output, &ascii[..ascii_staged]);

    println!("{}", str::from_utf8(&raw_output).unwrap());
}
