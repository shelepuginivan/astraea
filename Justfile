build: build-linux build-windows

build-linux:
    cargo build --release

build-windows:
    cargo build --target x86_64-pc-windows-gnu --release

package: \
    package-linux \
    package-windows \
    collect-checksums

package-linux: \
    build-linux \
    package-linux-prepare \
    package-linux-tarball \
    package-linux-clean

package-linux-prepare:
    mkdir -p dist/astraea-linux-x86_64/
    cp target/release/astraea dist/astraea-linux-x86_64/
    cp LICENSE dist/astraea-linux-x86_64/

[working-directory: 'dist']
package-linux-tarball:
    tar -czvf astraea-linux-x86_64.tar.gz astraea-linux-x86_64/

[working-directory: 'dist']
package-linux-clean:
    rm -rf astraea-linux-x86_64/

package-windows: \
    build-windows \
    package-windows-prepare \
    package-windows-zip \
    package-windows-clean

package-windows-prepare:
    mkdir -p dist/astraea-win-x86_64/
    cp target/release/astraea dist/astraea-win-x86_64/
    cp LICENSE dist/astraea-win-x86_64/

[working-directory: 'dist']
package-windows-zip:
    zip astraea-win-x86_64.zip -r astraea-win-x86_64/

[working-directory: 'dist']
package-windows-clean:
    rm -rf astraea-win-x86_64/

[working-directory: 'dist']
collect-checksums:
    sha256sum * > checksums

clean:
    rm -rf dist target
