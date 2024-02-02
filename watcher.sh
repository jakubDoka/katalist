while inotifywait -r -e modify . > /dev/null 2>&1; do
    sh -c "clear && $1"
done
